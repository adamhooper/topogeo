/// Reads ESRI ".shp" Shapefile, as per
/// https://www.esri.com/library/whitepapers/pdfs/shapefile.pdf
use std::error;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;
use byteorder::{BigEndian, ByteOrder, LittleEndian};
use itertools::Itertools;

const SHP_HEADER_LENGTH: usize = 100;
const SHP_RECORD_HEADER_LENGTH: usize = 8;
const SHP_MAGIC_NUMBER: u32 = 9994;
const SHP_VERSION: u32 = 1000;
const SHP_POINT_LENGTH: usize = 16;

#[derive(Debug)]
pub enum ShpError {
    IOError(io::Error),
    ParseError(String),
}

impl error::Error for ShpError {
    fn description(&self) -> &str {
        match *self {
            ShpError::IOError(ref err) => { err.description() },
            ShpError::ParseError(ref description) => { description },
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            ShpError::IOError(ref err) => { Some(err) },
            ShpError::ParseError(_) => { None },
        }
    }
}

impl fmt::Display for ShpError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ShpError::IOError(ref err) => { err.fmt(f) },
            ShpError::ParseError(ref description) => { write!(f, "Parse error: {}", description) },
        }
    }
}

#[derive(Debug,Copy,Clone)]
pub enum ShpShapeType {
    Null,
    Point,
    PolyLine,
    Polygon,
    MultiPoint,
    PointZ,
    PolyLineZ,
    PolygonZ,
    MultiPointZ,
    PointM,
    PolyLineM,
    PolygonM,
    MultiPointM,
    MultiPatch,
}

impl ShpShapeType {
    fn with_u32(u: u32) -> Option<ShpShapeType> {
        match u {
            0  => Some(ShpShapeType::Null),
            1  => Some(ShpShapeType::Point),
            3  => Some(ShpShapeType::PolyLine),
            5  => Some(ShpShapeType::Polygon),
            8  => Some(ShpShapeType::MultiPoint),
            11 => Some(ShpShapeType::PointZ),
            13 => Some(ShpShapeType::PolyLineZ),
            15 => Some(ShpShapeType::PolygonZ),
            18 => Some(ShpShapeType::MultiPointZ),
            21 => Some(ShpShapeType::PointM),
            23 => Some(ShpShapeType::PolyLineM),
            25 => Some(ShpShapeType::PolygonM),
            28 => Some(ShpShapeType::MultiPointM),
            31 => Some(ShpShapeType::MultiPatch),
            _ => None,
        }
    }
}

#[derive(Debug,Copy,Clone)]
pub struct ShpBoundingBox(pub f64, pub f64, pub f64, pub f64);

#[derive(Debug,Copy,Clone)]
pub struct ShpHeader {
    pub file_n_bytes: usize,
    pub shape_type: ShpShapeType,
    pub bounding_box: ShpBoundingBox,
}

#[derive(Debug,Clone)]
pub struct ShpPolygonRecord {
    pub record_number: u32,
    pub rings: Box<[ShpPolygonRing]>,
}

#[derive(Debug,Clone)]
pub struct ShpPolygonRing(pub Box<[ShpPoint]>);

impl fmt::Display for ShpPolygonRing {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut r = write!(f, "[");
        for (i, &point) in self.0.iter().enumerate() {
            if i > 0 {
                r = r.and_then(|_| write!(f, ","));
            }
            r = r.and_then(|_| write!(f, "{}", point));
        }
        r.and_then(|_| write!(f, "]"))
    }
}

#[derive(Debug,Clone,Copy,PartialEq,PartialOrd)]
pub struct ShpPoint(pub f64, pub f64);

impl fmt::Display for ShpPoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({},{})", self.0, self.1)
    }
}

/// Reads the first 100 bytes of the file.
///
/// Side-effect: advances the file cursor 100 bytes.
///
/// Returns Ok iff the file seems to be a valid Polygon shapefile. (Right now,
/// other shapefile formats such as PolygonZ, MultiPointM, etc., are not
/// supported; this method will return Err.)
fn read_shp_header(file: &mut io::Read) -> Result<ShpHeader, ShpError> {
    let mut buf = [ 0u8; SHP_HEADER_LENGTH ];

    match file.read_exact(&mut buf) {
        Err(err) => { Err(ShpError::IOError(err)) },
        Ok(_) => {
            let magic_number = BigEndian::read_u32(&buf[0..4]);
            let file_len = BigEndian::read_u32(&buf[24..28]);
            let version = LittleEndian::read_u32(&buf[28..32]);
            let shape_type_u32 = LittleEndian::read_u32(&buf[32..36]);
            let bounding_box = ShpBoundingBox(
                LittleEndian::read_f64(&buf[36..44]),
                LittleEndian::read_f64(&buf[44..52]),
                LittleEndian::read_f64(&buf[52..60]),
                LittleEndian::read_f64(&buf[60..68]),
            );

            if magic_number != SHP_MAGIC_NUMBER {
                return Err(ShpError::ParseError(format!("File has wrong magic number: found {}, expected {}", magic_number, SHP_MAGIC_NUMBER)));
            }

            if version != SHP_VERSION {
                return Err(ShpError::ParseError(format!("File has wrong version: found {}, expected {}", version, SHP_VERSION)));
            }

            match ShpShapeType::with_u32(shape_type_u32) {
                Some(ShpShapeType::Polygon) => {
                    Ok(ShpHeader {
                        file_n_bytes: (file_len * 2) as usize,
                        shape_type: ShpShapeType::Polygon,
                        bounding_box: bounding_box,
                    })
                }
                Some(unsupported) => {
                    Err(ShpError::ParseError(format!("File has unsupported type: found {:?}, expected {:?}", unsupported, ShpShapeType::Polygon)))
                }
                None => {
                    Err(ShpError::ParseError(format!("File has nonexistent data type {}", shape_type_u32)))
                }
            }
        }
    }
}

fn parse_point(buf: &[u8]) -> Result<ShpPoint, ShpError> {
    Ok(ShpPoint(
        LittleEndian::read_f64(&buf[0..8]),
        LittleEndian::read_f64(&buf[8..16])
    ))
}

fn parse_polygon_record(buf: &[u8], record_number: u32) -> Result<ShpPolygonRecord, ShpError> {
    let shape_type_u32 = LittleEndian::read_u32(&buf[0..4]);
    if shape_type_u32 != 5 {
        return Err(ShpError::ParseError(format!("Record number {} has unsupported shape type: found {}, expected {}", record_number, shape_type_u32, 5)));
    }

    let num_parts = LittleEndian::read_u32(&buf[36..40]) as usize;
    if num_parts == 0 {
        return Err(ShpError::ParseError(format!("Record number {} has no parts", record_number)));
    }

    let num_points = LittleEndian::read_u32(&buf[40..44]) as usize;

    let needed_len = (44 + 4 * num_parts + SHP_POINT_LENGTH * num_points) as usize;
    if needed_len != buf.len() {
        return Err(ShpError::ParseError(format!("Record number {} needs {} bytes (it has {} parts and {} points), but the record header says it has {} bytes", record_number, needed_len, num_parts, num_points, buf.len())));
    }

    let mut points = Vec::<ShpPoint>::with_capacity(num_points);
    for ref chunk in buf[44 + 4 * num_parts ..].chunks(SHP_POINT_LENGTH) {
        match parse_point(&chunk) {
            Err(err) => { return Err(err); }
            Ok(point) => { points.push(point); }
        }
    }

    let parts: Vec<usize> = buf[44 .. 44 + 4 * num_parts].chunks(4)
        .map(|ref b| LittleEndian::read_u32(&b) as usize)
        .collect();

    let mut rings = Vec::<ShpPolygonRing>::with_capacity(num_parts);
    for (&part_start, &part_end) in parts.iter().tuple_windows() {
        if part_start > points.len() || part_end > points.len() {
            return Err(ShpError::ParseError(format!("Record number {} has a ring with points {}-{}, but there are only {} points in the record", record_number, part_start, part_end, num_points)));
        }

        if part_start + 3 > part_end {
            return Err(ShpError::ParseError(format!("Record number {} has a ring with points {}-{}, but that's an invalid range", record_number, part_start, part_end)));
        }

        let mut copies = vec![ ShpPoint(0., 0.); part_end - part_start ].into_boxed_slice();
        copies.copy_from_slice(&points[part_start .. part_end ]);
        rings.push(ShpPolygonRing(copies));
    }

    let last_part = *parts.last().unwrap();
    if last_part + 3 >= points.len() {
        return Err(ShpError::ParseError(format!("Record number {} has a ring starting at point {}, but there are only {} points in the record", record_number, parts.last().unwrap(), num_points)));
    }
    let mut last_ring_copies = vec![ ShpPoint(0., 0.); num_points - last_part ].into_boxed_slice();
    last_ring_copies.copy_from_slice(&points[last_part .. num_points]);
    rings.push(ShpPolygonRing(last_ring_copies));

    Ok(ShpPolygonRecord{
        record_number: record_number,
        rings: rings.into_boxed_slice(),
    })
}

/// Reads the next Polygon record from the file, and returns the number of bytes
/// that polygon consumed (including its record header).
///
/// Side effect: advances the file cursor to the next Polygon.
fn read_polygon_record(file: &mut io::Read) -> Result<(ShpPolygonRecord, usize), ShpError> {
    let mut header_buf = [ 0u8; SHP_RECORD_HEADER_LENGTH ];

    match file.read_exact(&mut header_buf) {
        Err(err) => Err(ShpError::IOError(err)),
        Ok(_) => {
            let record_number = BigEndian::read_u32(&header_buf[0..4]);
            let content_length = BigEndian::read_u32(&header_buf[4..8]) as usize;

            let mut buf = vec![ 0u8; content_length * 2 ];
            match file.read_exact(&mut buf) {
                Err(err) => Err(ShpError::IOError(err)),
                Ok(_) => parse_polygon_record(&buf[..], record_number).map(|record| (record, header_buf.len() + buf.len()))
            }
        }
    }
}

#[derive(Debug)]
pub struct ShpReader<R: io::Read> {
    file: R,
    pub n_bytes_already_read: usize,
    pub header: ShpHeader,
}

/// Reads an ESRI ".shp" Shapefile, following instructions at
/// https://www.esri.com/library/whitepapers/pdfs/shapefile.pdf
///
/// # Example
///
/// ```
/// use std::fs;
/// use std::io;
/// use topogeo::read::shapefile::shp::{ShpPoint, ShpReader};
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/shp/simple.shp");
///
/// let f = fs::File::open(&path).unwrap();
/// let r = io::BufReader::new(f);
///
/// // builder returns Result<ShpReader, ShpError>
/// let mut shp_reader = ShpReader::new(r).unwrap();
///
/// assert_eq!(220, shp_reader.header.file_n_bytes);
///
/// // shp_reader.next(), an Iterator method, returns
/// // Option<Result<ShpPolygonRecord, ShpError>>
/// let polygon = shp_reader.next().unwrap().unwrap();
///
/// assert_eq!(1, polygon.rings.len());
/// assert_eq!(4, polygon.rings[0].0.len());
/// assert_eq!(ShpPoint(7631181.2140951585, 1241556.341007172), polygon.rings[0].0[0]);
/// ```
impl<R: io::Read> ShpReader<R> {
    pub fn new(mut file: R) -> Result<ShpReader<R>, ShpError> {
        read_shp_header(&mut file).map(move |shp_header| {
            ShpReader::<R> {
                file: file,
                n_bytes_already_read: SHP_HEADER_LENGTH,
                header: shp_header,
            }
        })
    }
}

impl<R: io::Read> Iterator for ShpReader<R> {
    type Item = Result<ShpPolygonRecord, ShpError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.n_bytes_already_read >= self.header.file_n_bytes {
            None
        } else {
            match read_polygon_record(&mut self.file) {
                Err(err) => Some(Err(err)),
                Ok((record, n_bytes)) => {
                    self.n_bytes_already_read += n_bytes;
                    if self.n_bytes_already_read > self.header.file_n_bytes {
                        Some(Err(ShpError::ParseError(format!("The Shapefile header suggests the file is {} bytes long, but it's longer than that.", self.header.file_n_bytes))))
                    } else {
                        Some(Ok(record))
                    }
                }
            }
        }
    }
}

/// Reads an ESRI ".shp" Shapefile, following instructions at
/// https://www.esri.com/library/whitepapers/pdfs/shapefile.pdf
///
/// # Example
///
/// ```
/// use topogeo::read::shapefile::shp;
///
/// # let mut path = std::env::current_dir().unwrap();
/// # path.push("test/read/shapefile/shp/simple.shp");
///
/// // builder returns Result<shp::ShpReader, shp::ShpError>
/// let mut shp_reader = shp::open(&path).unwrap();
///
/// assert_eq!(220, shp_reader.header.file_n_bytes);
///
/// // shp_reader.next(), an Iterator method, returns
/// // Option<Result<shp::ShpPolygonRecord, shp::ShpError>>
/// let polygon = shp_reader.next().unwrap().unwrap();
///
/// assert_eq!(1, polygon.rings.len());
/// assert_eq!(4, polygon.rings[0].0.len());
/// assert_eq!(shp::ShpPoint(7631181.2140951585, 1241556.341007172), polygon.rings[0].0[0]);
/// ```
pub fn open(path: &Path) -> Result<ShpReader<io::BufReader<fs::File>>, ShpError> {
    match fs::File::open(path) {
        Err(err) => Err(ShpError::IOError(err)),
        Ok(f) => {
            let r = io::BufReader::new(f);
            ShpReader::new(r)
        }
    }
}
