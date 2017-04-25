use std::error;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::io;
use encoding;
use super::dbf;
use super::shp;

/// Iterates over ".shp" and ".dbf" records simultaneously.
///
/// # Examples
///
/// ```
/// # extern crate encoding;
/// # extern crate topogeo;
///
/// # fn main() {
///   use std::fs;
///   use std::io;
///   use encoding;
///   use topogeo::read::shapefile::shapefile::ShapefileReader;
///   use topogeo::read::shapefile::shp;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/simple.shp");
///
///   let shp_f = io::BufReader::new(fs::File::open(&path).unwrap());
///   path.set_extension("dbf");
///   let dbf_f = io::BufReader::new(fs::File::open(&path).unwrap());
///
///   let enc = encoding::label::encoding_from_whatwg_label("utf-8").unwrap();
///
///   // builder returns Result<ShapefileReader, ShapefileError>
///   let mut reader = ShapefileReader::new(shp_f, dbf_f, enc).unwrap();
///
///   // get_field() method returns Option<DbfField>
///   let foo = reader.get_field("foo").unwrap();
///
///   // dbf_reader.next(), an Iterator method, returns
///   // Option<Result<ShapefileRecord, ShapefileError>>
///   let record = reader.next().unwrap().unwrap();
///
///   // DbfField::read_string() returns Result<String, DbfError::ParseError>
///   assert_eq!("bar".to_string(), foo.read_string(&record.data).unwrap());
///
///   // rings are Box<[shp::PolygonRing]>
///   assert_eq!(1, record.rings.len());
///   assert_eq!(4, record.rings[0].0.len());
///   assert_eq!(shp::ShpPoint(295., -249.), record.rings[0].0[0]);
///
///   // let's say this file has two records....
///   let record2 = reader.next();
///   assert!(record2.is_some());
///   assert!(record2.unwrap().is_ok());
///
///   // that means the iterator will stop at number three
///   assert!(reader.next().is_none());
///
///   // Of course, this could have been a for-loop:
///   // for record_result in reader {
///   //   match record_result {
///   //     Ok(record) => { ... },
///   //     Err(err) => { ...; break; },
///   //   }
///   // }
/// # }
/// ```
#[derive(Debug)]
pub struct ShapefileReader<R: io::Read, S: io::Read> {
    shp_reader: shp::ShpReader<R>,
    dbf_reader: dbf::DbfReader<S>,
}

#[derive(Debug)]
pub enum ShapefileError {
    ShpError(shp::ShpError),
    DbfError(dbf::DbfError),
    JoinError(String),
}

impl error::Error for ShapefileError {
    fn description(&self) -> &str {
        match *self {
            ShapefileError::ShpError(ref err) => err.description(),
            ShapefileError::DbfError(ref err) => err.description(),
            ShapefileError::JoinError(ref description) => description,
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            ShapefileError::ShpError(ref err) => Some(err),
            ShapefileError::DbfError(ref err) => Some(err),
            ShapefileError::JoinError(_) => None,
        }
    }
}

impl fmt::Display for ShapefileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ShapefileError::ShpError(ref err) => err.fmt(f),
            ShapefileError::DbfError(ref err) => err.fmt(f),
            ShapefileError::JoinError(ref description) => write!(f, "Parse error: {}", description),
        }
    }
}

#[derive(Debug)]
pub struct ShapefileRecord {
    pub rings: Box<[shp::ShpPolygonRing]>,
    pub data: dbf::DbfRecord,
}

impl<R: io::Read, S: io::Read> ShapefileReader<R, S> {
    pub fn new(r: R, s: S, encoding: encoding::EncodingRef) -> Result<ShapefileReader<R, S>, ShapefileError> {
        match (shp::ShpReader::new(r), dbf::DbfReader::new(s, encoding)) {
            // Check failures
            (Err(err), _) => Err(ShapefileError::ShpError(err)),
            (_, Err(err)) => Err(ShapefileError::DbfError(err)),

            (Ok(shp_reader), Ok(dbf_reader)) => {
                Ok(ShapefileReader {
                    shp_reader: shp_reader,
                    dbf_reader: dbf_reader
                })
            }
        }
    }

    pub fn dbf_fields(&self) -> Box<[dbf::DbfField]> {
        self.dbf_reader.meta.fields.clone()
    }

    pub fn get_field(&self, name: &str) -> Option<dbf::DbfField> {
        self.dbf_reader.get_field(name)
    }
}

impl<R: io::Read, S: io::Read> Iterator for ShapefileReader<R, S> {
    type Item = Result<ShapefileRecord, ShapefileError>;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.shp_reader.next(), self.dbf_reader.next()) {
            // Check for end of files
            (None, None) => None,
            (Some(_), None) => Some(Err(ShapefileError::JoinError("'.shp' file has more records than '.dbf' record".to_string()))),
            (None, Some(_)) => Some(Err(ShapefileError::JoinError("'.dbf' file has more records than '.shp' record".to_string()))),

            // check for errors
            (Some(Err(err)), _) => Some(Err(ShapefileError::ShpError(err))),
            (_, Some(Err(err))) => Some(Err(ShapefileError::DbfError(err))),

            // we have records!
            (Some(Ok(shape)), Some(Ok(data))) => {
                Some(Ok(ShapefileRecord {
                    rings: shape.rings,
                    data: data,
                }))
            }
        }
    }
}

/// Open by ".shp" filename.
///
/// This will automatically search for the accompanying ".dbf"; it will fail
/// if that file does not exist.
///
/// # Example
///
/// ```
/// # extern crate encoding;
/// # extern crate topogeo;
///
/// # fn main() {
/// use topogeo::read::shapefile::shapefile;
/// use encoding;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/simple.shp");
/// let reader = shapefile::open(&path, encoding::all::UTF_8).unwrap();
///
/// for record in reader {
///     // record is a Result<ShapefileRecord, ShapefileError>
///     println!("{:?}", record.unwrap());
/// }
/// # }
/// ```
pub fn open(shp_path: &Path, encoding: encoding::EncodingRef) -> Result<ShapefileReader<io::BufReader<fs::File>, io::BufReader<fs::File>>, ShapefileError> {
    match shp::open(shp_path) {
        Err(err) => Err(ShapefileError::ShpError(err)),
        Ok(shp_reader) => {
            let mut dbf_path = PathBuf::from(shp_path);
            dbf_path.set_extension("dbf");

            match dbf::open(dbf_path.as_path(), encoding) {
                Err(err) => Err(ShapefileError::DbfError(err)),
                Ok(dbf_reader) => {
                    Ok(ShapefileReader {
                        shp_reader: shp_reader,
                        dbf_reader: dbf_reader,
                    })
                }
            }
        }
    }
}
