/// Reads xbase ".dbf" file, as per
/// https://www.clicketyclick.dk/databases/xbase/format/dbf.html

use std::error;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;
use std::sync::Arc;
use byteorder::{ByteOrder, LittleEndian};
use encoding;

#[derive(Debug)]
pub enum DbfType {
    Unsupported,
    Char,
    Numeric,
    Float,
    Long,
    Double,
}

#[derive(Debug)]
pub struct DbfField {
    name: String,
    data_type: DbfType,
    offset: u16,
    len: u8,
    decimal_count: u8,
}

const DBF_HEADER_LENGTH: usize = 32;
const DBF_FIELD_DESCRIPTOR_LENGTH: usize = 32;

#[derive(Debug)]
struct DbfHeader {
    n_records: usize,
    n_header_bytes: usize,
    n_bytes_per_record: usize,
}

pub struct DbfMeta {
    n_records: usize,
    n_bytes_per_record: usize,
    fields: Box<[DbfField]>,
    encoding: encoding::EncodingRef,
}

// encoding::EncodingRef does not implement std::fmt::Debug
impl fmt::Debug for DbfMeta {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("DbfMeta")
            .field("n_records", &self.n_records)
            .field("n_bytes_per_record", &self.n_bytes_per_record)
            .field("fields", &self.fields)
            .field("encoding", &self.encoding.name())
            .finish()
    }
}

#[derive(Debug)]
pub struct DbfRecord {
    meta: Arc<DbfMeta>,
    bytes: Box<[u8]>,
}

impl DbfRecord {
    pub fn field_to_string(&self, field: &DbfField) -> String {
        unreachable!()
    }
}

#[derive(Debug)]
pub enum DbfError {
    IOError(io::Error),
    ParseError(String),
}

impl error::Error for DbfError {
    fn description(&self) -> &str {
        match *self {
            DbfError::IOError(ref err) => { err.description() },
            DbfError::ParseError(ref description) => { description },
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            DbfError::IOError(ref err) => { Some(err) },
            DbfError::ParseError(_) => { None },
        }
    }
}

impl fmt::Display for DbfError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DbfError::IOError(ref err) => { err.fmt(f) },
            DbfError::ParseError(ref description) => { write!(f, "Parse error: {}", description) },
        }
    }
}

/// Reads the first 32 bytes of the file.
///
/// Side-effect: advances the file cursor 32 bytes.
fn read_dbf_header(file: &mut io::Read) -> Result<DbfHeader, DbfError> {
    let mut buf: [ u8; DBF_HEADER_LENGTH ] = [ 0; DBF_HEADER_LENGTH ];

    match file.read_exact(&mut buf) {
        Err(err) => { Err(DbfError::IOError(err)) },
        Ok(_) => {
            // It's hard to come up with a ParseError, because virtually any
            // combination of 32 bytes is a valid .dbf header.
            //
            // The one exception: invalid dates. bytes 1-3 (base 0) are "YMD"
            // in hex. All years are valid; there are 12 valid months and 31
            // valid days.
            if buf[2] > 12 || buf[3] > 31 {
                Err(DbfError::ParseError(String::from("The first four bytes of the file mention an invalid creation date. This is not a valid .dbf file.")))
            } else {
                Ok(DbfHeader {
                    n_records: LittleEndian::read_u32(&buf[4..]) as usize,
                    n_header_bytes: LittleEndian::read_u16(&buf[8..]) as usize,
                    n_bytes_per_record: LittleEndian::read_u16(&buf[10..]) as usize,
                })
            }
        }
    }
}

/// Reads all field definitions from the file.
///
/// Assumes exactly DBF_HEADER_LENGTH bytes of the file have been read already.
/// In other words, call this after read_dbf_header().
///
/// Side-effect: advances the file cursor to the first data record.
fn read_dbf_fields(file: &mut io::Read, dbf_header: &DbfHeader) -> Result<Box<[DbfField]>, DbfError> {
    let mut buf = vec![ 0u8; dbf_header.n_header_bytes - DBF_HEADER_LENGTH ];

    match file.read_exact(&mut buf) {
        Err(err) => { Err(DbfError::IOError(err)) },
        Ok(_) => {
            Ok(vec![].into_boxed_slice())
        }
    }
}

/// Reads the header, including field definitions, from a .dbf file.
///
/// Assumes the cursor is at the start of the file.
///
/// Side-effect: advances the file cursor to the first data record.
fn read_dbf_meta(file: &mut io::Read, encoding: encoding::EncodingRef) -> Result<DbfMeta, DbfError> {
    read_dbf_header(file).and_then(|dbf_header| {
        read_dbf_fields(file, &dbf_header).map(|dbf_fields| {
            DbfMeta {
                n_records: dbf_header.n_records,
                n_bytes_per_record: dbf_header.n_bytes_per_record,
                fields: dbf_fields,
                encoding: encoding
            }
        })
    })
}

/// Reads a single record from a .dbf file.
///
/// Assumes the cursor is at the start of the record and that the record
/// "should" exist (i.e., the header leads us to believe there's a record
/// here).
///
/// Side-effect: advances the file cursor to the next record.
fn read_dbf_record(file: &mut io::Read, dbf_meta: Arc<DbfMeta>) -> Result<DbfRecord, DbfError> {
    let mut buf = vec![ 0u8; dbf_meta.n_bytes_per_record ];

    match file.read_exact(&mut buf) {
        Err(err) => { Err(DbfError::IOError(err)) },
        Ok(_) => {
            Ok(DbfRecord {
                meta: dbf_meta,
                bytes: buf.into_boxed_slice(),
            })
        }
    }
}

/// Reads an xBase ".dbf" file, following instructions at
/// https://www.clicketyclick.dk/databases/xbase/format/dbf.html
///
/// # Example
///
/// ```TODO
/// use topogeo::read::shapefile::dbf::DbfReader;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/dbf/string-test.dbf");
/// let dbf_reader = DbfReader::with_path_ascii(&path).unwrap();
/// for record in dbf_reader {
///     println!("{:?}", record);
/// }
/// ```
pub struct DbfReader<R: io::Read> {
    file: R,
    n_records_already_iterated: usize,
    meta: Arc<DbfMeta>,
}

/// Opens an xBase ".dbf" file from the filesystem, following instructions at
/// https://www.clicketyclick.dk/databases/xbase/format/dbf.html
///
/// # Example
///
/// ```
/// # extern crate encoding;
/// # extern crate topogeo;
///
/// # fn main() {
/// use topogeo::read::shapefile::dbf;
/// use encoding;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/dbf/string-test.dbf");
/// let dbf_reader = dbf::open(&path, encoding::all::UTF_8).unwrap();
/// for record in dbf_reader {
///     println!("{:?}", record);
/// }
/// # }
/// ```
pub fn open(path: &Path, encoding: encoding::EncodingRef) -> Result<DbfReader<io::BufReader<fs::File>>, DbfError> {
    match fs::File::open(path) {
        Err(err) => { Err(DbfError::IOError(err)) },
        Ok(f) => {
            let r = io::BufReader::new(f);
            DbfReader::new(r, encoding)
        }
    }
}

/// Opens an xBase ".dbf" file from the filesystem, following instructions at
/// https://www.clicketyclick.dk/databases/xbase/format/dbf.html
///
/// # Example
///
/// ```
/// use topogeo::read::shapefile::dbf;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/dbf/string-test.dbf");
/// let dbf_reader = dbf::open_ascii(&path).unwrap();
/// for record in dbf_reader {
///     println!("{:?}", record);
/// }
/// ```
pub fn open_ascii(path: &Path) -> Result<DbfReader<io::BufReader<fs::File>>, DbfError> {
    let ascii = encoding::label::encoding_from_whatwg_label(&"ascii").unwrap();
    open(path, ascii)
}

impl<R: io::Read> DbfReader<R> {
    pub fn new(mut file: R, encoding: encoding::EncodingRef) -> Result<DbfReader<R>, DbfError> {
        read_dbf_meta(&mut file, encoding).map(move |dbf_meta| {
            DbfReader::<R> {
                file: file,
                n_records_already_iterated: 0,
                meta: Arc::new(dbf_meta),
            }
        })
    }
}

impl<R: io::Read> Iterator for DbfReader<R> {
    type Item = Result<DbfRecord, DbfError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.n_records_already_iterated == self.meta.n_records {
            None
        } else {
            let ret = read_dbf_record(&mut self.file, self.meta.clone());
            self.n_records_already_iterated += 1;
            Some(ret)
        }
    }
}
