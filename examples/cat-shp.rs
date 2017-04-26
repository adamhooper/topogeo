extern crate topogeo;

use std::env;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process;
use topogeo::read::shapefile;

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
        Ok(reader) => {
            let mut n_records: usize = 0;

            for record_result in reader {
                match record_result {
                    Err(err) => {
                        writeln!(&mut io::stderr(), "Error during read: {}", err).unwrap();
                        process::exit(1);
                    }
                    Ok(record) => {
                        n_records += 1;
                        println!("{}", record);
                    }
                }
            }

            println!("Read {} records", n_records);
        }
    }
}
