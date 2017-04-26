//! Reads ".shp" and accompanying ".dbf" files.
//!
//! There are two pieces of information ".shp" and ".dbf" files _don't_
//! contain:
//!
//! * The _projection_ isn't specified. Sometimes there's a ".prj" file that
//!   contains that information, but no file format can represent all the
//!   projections out there in the world. This library ignores the file and
//!   returns `f64` points.
//!
//! # Examples
//!
//! Open by ".shp" filename:
//!
//! ```
//! use topogeo::read::shapefile;
//!
//! # let mut path = std::env::current_dir().unwrap();
//! # path.push("test/read/shapefile/simple.shp");
//! let reader = shapefile::open_utf8(&path).unwrap();
//!
//! for record in reader {
//!     // record is a Result<ShapefileRecord, ShapefileError>
//!     println!("{:?}", record.unwrap());
//! }
//! ```
//!
//! Open by `io::Read` implementor (works best with `io::BufReader`):
//!
//! ```
//! # extern crate encoding;
//! # extern crate topogeo;
//!
//! # fn main() {
//! use std::fs;
//! use std::io;
//! use topogeo::read::shapefile;
//! use encoding;
//!
//! # let mut path = std::env::current_dir().unwrap();
//! # path.push("test/read/shapefile/simple.shp");
//! let shp_r = io::BufReader::new(fs::File::open(&path).unwrap());
//! path.set_extension("dbf");
//! let dbf_r = io::BufReader::new(fs::File::open(&path).unwrap());
//!
//! let reader = shapefile::ShapefileReader::new(shp_r, dbf_r, encoding::all::UTF_8).unwrap();
//!
//! for record in reader {
//!     // record is a Result<ShapefileRecord, ShapefileError>
//!     println!("{:?}", record.unwrap());
//! }
//! # }
//! ```
//!
//! Dump DBF data:
//!
//! ```
//! use topogeo::read::shapefile;
//!
//! # let mut path = std::env::current_dir().unwrap();
//! # path.push("test/read/shapefile/simple.shp");
//! let reader = shapefile::open_utf8(&path).unwrap();
//!
//! let fields = reader.dbf_fields();
//!
//! for record_result in reader {
//!     let record = record_result.unwrap();
//!
//!     for field in fields.iter() {
//!         let value_result = field.read_string(&record.data);
//!         print!("{}: {}; ", field.name, value_result.unwrap());
//!     }
//!     println!("");
//! }
//! ```

use std::fs;
use std::io;
use std::path::Path;
use encoding;

pub mod dbf;
pub mod shp;
pub mod shapefile;
pub mod geo;

pub use self::dbf::{DbfField, DbfRecord};
pub use self::shp::{ShpBoundingBox, ShpPoint, ShpPolygonRecord, ShpPolygonRing};
pub use self::shapefile::{ShapefileError, ShapefileReader};
pub use self::shapefile::open;
pub use self::geo::ShapefileGeoIterator;

pub fn open_ascii(shp_path: &Path) -> Result<ShapefileReader<io::BufReader<fs::File>, io::BufReader<fs::File>>, ShapefileError> {
    open(shp_path, encoding::all::ASCII)
}

pub fn open_utf8(shp_path: &Path) -> Result<ShapefileReader<io::BufReader<fs::File>, io::BufReader<fs::File>>, ShapefileError> {
    open(shp_path, encoding::all::UTF_8)
}

pub fn open_windows1252(shp_path: &Path) -> Result<ShapefileReader<io::BufReader<fs::File>, io::BufReader<fs::File>>, ShapefileError> {
    open(shp_path, encoding::all::WINDOWS_1252)
}
