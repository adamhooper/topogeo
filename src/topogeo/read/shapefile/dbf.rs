/// Reads xbase ".dbf" file, as per
/// https://www.clicketyclick.dk/databases/xbase/format/dbf.html

use std::error;
use std::fmt;
use std::io;
use std::sync::Arc;
use byteorder::{ByteOrder, LittleEndian};
use encoding::{CodecError, Encoding};

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

#[derive(Debug)]
pub struct DbfMeta {
    n_records: usize,
    n_bytes_per_record: usize,
    fields: Box<[DbfField]>,
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

pub struct DbfReader<'a, F: 'a+io::Read> {
    file: &'a mut F,
    n_records_already_iterated: usize,
    meta: Arc<DbfMeta>,
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
fn read_dbf_meta(file: &mut io::Read) -> Result<DbfMeta, DbfError> {
    read_dbf_header(file).and_then(|dbf_header| {
        read_dbf_fields(file, &dbf_header).map(|dbf_fields| {
            DbfMeta {
                n_records: dbf_header.n_records,
                n_bytes_per_record: dbf_header.n_bytes_per_record,
                fields: dbf_fields,
            }
        })
    })
}

#[derive(Debug)]
pub enum DbfReadResult {
    Record(DbfRecord),
    Err(DbfError),
    Eof,
}

/// Reads a single record from a .dbf file.
///
/// Assumes the cursor is at the start of the record and that the record
/// "should" exist (i.e., the header leads us to believe there's a record
/// here).
///
/// Side-effect: advances the file cursor to the next record.
fn read_dbf_record(file: &mut io::Read, dbf_meta: Arc<DbfMeta>) -> DbfReadResult {
    let mut buf = vec![ 0u8; dbf_meta.n_bytes_per_record ];

    match file.read_exact(&mut buf) {
        Err(err) => { DbfReadResult::Err(DbfError::IOError(err)) },
        Ok(_) => {
            DbfReadResult::Record(DbfRecord {
                meta: dbf_meta,
                bytes: buf.into_boxed_slice(),
            })
        }
    }
}

impl<'a, F: io::Read> DbfReader<'a, F> {
    pub fn new(file: &'a mut F, encoding: &Encoding) -> Result<DbfReader<'a, F>, DbfError> {
        read_dbf_meta(file).map(move |dbf_meta| {
            DbfReader::<'a, F> {
                file: file,
                n_records_already_iterated: 0,
                meta: Arc::new(dbf_meta),
            }
        })
    }

    pub fn next(&mut self) -> DbfReadResult {
        if self.n_records_already_iterated == self.meta.n_records {
            DbfReadResult::Eof
        } else {
            let ret = read_dbf_record(self.file, self.meta.clone());
            self.n_records_already_iterated += 1;
            ret
        }
    }
}
