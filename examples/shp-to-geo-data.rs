extern crate topogeo;

use std::env;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process;
use topogeo::read::shapefile;

/// Reads the given .shp file and outputs it as `geo::Region`s -- data with
/// `u32`-scaled outer and inner rings.
fn main() {
    let mut args = env::args();

    if args.len() != 2 {
        writeln!(&mut io::stderr(), "Usage: {} <SHP_PATH>", args.next().unwrap()).unwrap();
        process::exit(1);
    }

    args.next();
    let path = PathBuf::from(args.next().unwrap());

    match shapefile::open_windows1252(&path) {
        Err(err) => {
            writeln!(&mut io::stderr(), "{}", err).unwrap();
            process::exit(1);
        }
        Ok(mut reader) => {
            let mut n_regions: usize = 0;

            for region_result in shapefile::ShapefileGeoIterator::new(&mut reader) {
                match region_result {
                    Err(err) => {
                        writeln!(&mut io::stderr(), "Error during read: {}", err).unwrap();
                        process::exit(1);
                    }
                    Ok(region) => {
                        println!("{}", region);
                        n_regions += 1;
                    }
                }
            }

            println!("Read {} regions", n_regions);
        }
    }
}
