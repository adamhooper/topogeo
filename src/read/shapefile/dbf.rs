/// Reads xBase ".dbf" file, as per
/// https://www.clicketyclick.dk/databases/xbase/format/dbf.html

use std::error;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;
use std::sync::Arc;
use byteorder::{ByteOrder, LittleEndian};
use encoding;
use regex;

#[derive(Copy,Clone)]
pub enum DbfType {
    Character(encoding::EncodingRef),
    Numeric,
    Logical,
    Date,
    FloatingPoint,
    Timestamp,
    Double,
    Long,
    Unsupported,
}

// encoding::EncodingRef does not implement std::fmt::Debug
impl fmt::Debug for DbfType {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DbfType::Character(encoding) => {
                fmt.debug_struct("DbfType::Character")
                    .field("encoding", &encoding.name())
                    .finish()
            }
            &DbfType::Numeric => { write!(fmt, "DbfType::Numeric") }
            &DbfType::Logical => { write!(fmt, "DbfType::Logical") }
            &DbfType::Date => { write!(fmt, "DbfType::Date") }
            &DbfType::FloatingPoint => { write!(fmt, "DbfType::FloatingPoint") }
            &DbfType::Timestamp => { write!(fmt, "DbfType::Timestamp") }
            &DbfType::Double => { write!(fmt, "DbfType::Double") }
            &DbfType::Long => { write!(fmt, "DbfType::Long") }
            &DbfType::Unsupported => { write!(fmt, "DbfType::Unsupported") }
        }
    }
}

impl DbfType {
    fn with_code(u: u8, encoding: encoding::EncodingRef) -> DbfType {
        match u as char {
            'C' => { DbfType::Character(encoding) },
            'N' => { DbfType::Numeric },
            'L' => { DbfType::Logical },
            'D' => { DbfType::Date },
            'F' => { DbfType::FloatingPoint },
            '@' => { DbfType::Timestamp },
            'O' => { DbfType::Double },
            '+' | '|' => { DbfType::Long },
            _ => { DbfType::Unsupported }
        }
    }
}

#[derive(Debug,Clone)]
pub struct DbfField {
    pub name: String,
    data_type: DbfType,
    offset: usize,
    len: usize,
}

fn trim_end_spaces(bytes: &[u8]) -> &[u8] {
    let n_ending_spaces = bytes.iter().rev().position(|&b| b != 0x20u8).unwrap_or(bytes.len());
    &bytes[.. bytes.len() - n_ending_spaces]
}

fn dbf_numeric_to_valid_string(bytes: &[u8]) -> Result<String, DbfError> {
    lazy_static! {
        static ref RE: regex::bytes::Regex = regex::bytes::Regex::new("^ *(-?[0-9]+(?:\\.[0-9]+)?)$").unwrap();
    }
    match RE.captures(bytes) {
        None => Err(DbfError::ParseError(String::from("Bytes in numeric record do not represent a number"))),
        Some(c) => {
            let byte_slice = c.get(1).unwrap().as_bytes();
            Ok(String::from_utf8(byte_slice.to_vec()).unwrap())
        }
    }
}

impl DbfField {
    pub fn read_string(&self, record: &DbfRecord) -> Result<String, DbfError> {
        let bytes = &record.bytes[self.offset .. self.offset + self.len];

        match &self.data_type {
            &DbfType::Character(encoding) => {
                encoding.decode(trim_end_spaces(bytes), encoding::DecoderTrap::Strict)
                    .map_err(|s| DbfError::ParseError(s.to_string()))
            }
            &DbfType::Long => Ok(LittleEndian::read_u32(bytes).to_string()),
            &DbfType::Numeric => {
                dbf_numeric_to_valid_string(bytes)
            }
            _ => { unimplemented!() }
        }
    }
}

const DBF_HEADER_LENGTH: usize = 32;
const DBF_FIELD_DESCRIPTOR_LENGTH: usize = 32;

#[derive(Debug,Copy,Clone)]
struct DbfHeader {
    pub n_records: usize,
    pub n_header_bytes: usize,
    pub n_bytes_per_record: usize,
}

#[derive(Debug)]
pub struct DbfMeta {
    pub n_records: usize,
    pub n_bytes_per_record: usize,
    pub fields: Box<[DbfField]>,
}

#[derive(Debug)]
pub struct DbfRecord {
    meta: Arc<DbfMeta>,
    pub bytes: Box<[u8]>,
}

impl fmt::Display for DbfRecord {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::new();

        for (i, ref field) in self.meta.fields.iter().enumerate() {
            if i != 0 {
                s.push_str("; ");
            }

            match field.read_string(self) {
                Err(err) => {
                    return write!(f, "{{Invalid DBF record: {:?}}}", err);
                },
                Ok(value) => {
                    s.push_str(field.name.as_str());
                    s.push(':');
                    s.push_str(value.as_str());
                }
            }
        }

        write!(f, "{{{}}}", s)
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

fn parse_dbf_field(bytes: &[u8], encoding: encoding::EncodingRef, offset: usize) -> Result<DbfField, DbfError> {
    let last_index = bytes[0 .. 11].iter().position(|&x| x == 0u8).unwrap_or(11);
    match encoding.decode(&bytes[0 .. last_index], encoding::DecoderTrap::Strict) {
        Err(_) => { Err(DbfError::ParseError(String::from("Field name is not valid ") + encoding.name())) },
        Ok(name) => {
            Ok(DbfField {
                name: name,
                data_type: DbfType::with_code(bytes[11], encoding),
                offset: offset,
                len: bytes[16] as usize
            })
        }
    }
}

/// Reads all field definitions from the file.
///
/// Assumes exactly DBF_HEADER_LENGTH bytes of the file have been read already.
/// In other words, call this after read_dbf_header().
///
/// Side-effect: advances the file cursor to the first data record.
fn read_dbf_fields(file: &mut io::Read, encoding: encoding::EncodingRef, dbf_header: &DbfHeader) -> Result<Box<[DbfField]>, DbfError> {
    let mut buf = vec![ 0u8; dbf_header.n_header_bytes - DBF_HEADER_LENGTH ];

    match file.read_exact(&mut buf) {
        Err(err) => { Err(DbfError::IOError(err)) },
        Ok(_) => {
            let mut v = Vec::<DbfField>::with_capacity(buf.len() / DBF_FIELD_DESCRIPTOR_LENGTH);
            let mut offset = 1; // 0 is "deleted" flag

            for chunk in buf.chunks(DBF_FIELD_DESCRIPTOR_LENGTH) {
                if chunk.len() != DBF_FIELD_DESCRIPTOR_LENGTH {
                    break;
                }

                match parse_dbf_field(&chunk, encoding, offset) {
                    Err(err) => { return Err(err) },
                    Ok(next) => {
                        offset += next.len;
                        v.push(next);
                    }
                }
            }

            Ok(v.into_boxed_slice())
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
        read_dbf_fields(file, encoding, &dbf_header).map(|dbf_fields| {
            DbfMeta {
                n_records: dbf_header.n_records,
                n_bytes_per_record: dbf_header.n_bytes_per_record,
                fields: dbf_fields,
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
/// ```
/// # extern crate encoding;
/// # extern crate topogeo;
///
/// # fn main() {
///   use std::fs;
///   use std::io;
///   use encoding;
///   use topogeo::read::shapefile::dbf::DbfReader;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/dbf/string-test.dbf");
///
///   let f = fs::File::open(&path).unwrap();
///   let r = io::BufReader::new(f);
///
///   let enc = encoding::label::encoding_from_whatwg_label("ascii").unwrap();
///
///   // builder returns Result<DbfReader, DbfError>
///   let mut dbf_reader = DbfReader::new(r, enc).unwrap();
///
///   println!("{:?}", dbf_reader.meta);
///
///   // get_field() method returns Option<DbfField>
///   let foo = dbf_reader.get_field("foo").unwrap();
///
///   // dbf_reader.next(), an Iterator method, returns
///   // Option<Result<DbfRecord, DbfError>>
///   dbf_reader.next();
///   let record = dbf_reader.next().unwrap().unwrap();
///
///   // DbfField::read_string() returns Result<String, DbfError::ParseError>
///   assert_eq!(String::from("bar"), foo.read_string(&record).unwrap());
/// # let record = dbf_reader.next().unwrap().unwrap();
/// # assert_eq!(String::from("baz"), foo.read_string(&record).unwrap());
/// # }
/// ```
#[derive(Debug)]
pub struct DbfReader<R: io::Read> {
    file: R,
    pub n_records_already_iterated: usize,
    pub meta: Arc<DbfMeta>,
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

    pub fn get_field(&self, name: &str) -> Option<DbfField> {
        for field in &*self.meta.fields {
            if field.name == name {
                return Some(field.clone())
            }
        }

        return None
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
