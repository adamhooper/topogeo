extern crate topogeo;

use std::env;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process;
use topogeo::clip;
use topogeo::read::shapefile;
use topogeo::topology;

fn print_topology_description<Data>(topology: &topology::Topology<Data>) {
    let mut n_outer_rings = 0;
    let mut n_inner_rings = 0;

    for ref region in topology.regions.iter() {
        n_outer_rings += region.outer_rings.len();
        n_inner_rings += region.inner_rings.len();
    }

    let mut n_shared_edges = 0;
    let mut n_lone_edges = 0;
    let mut n_points = 0;

    for ref edge in topology.edges.iter() {
        if edge.rings[1].is_null() {
            n_lone_edges += 1;
        } else {
            n_shared_edges += 1;
        }
        n_points += edge.points.len();
    }

    println!("  Regions:      {}", topology.regions.len());
    println!("  Outer rings:  {}", n_outer_rings);
    println!("  Inner rings:  {}", n_inner_rings);
    println!("  Edges:        {}", topology.edges.len());
    println!("  Shared edges: {}", n_shared_edges);
    println!("  Lone edges:   {}", n_lone_edges);
    println!("  Points:       {}", n_points);
}

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

    let mut builder = topology::TopologyBuilder::new();

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
                        builder.add_region(region);
                        n_regions += 1;
                    }
                }
            }

            println!("Read {} regions", n_regions);
        }
    }

    let topology = builder.into_topology();
    println!("Formed initial topology:");
    print_topology_description(&topology);

    let normalized = topogeo::normalize(&topology);
    println!("Normalized topology:");
    print_topology_description(&normalized);

    let clipped = clip::clip_topology(&normalized, &clip::ClipMask::MinX(1u32 << 31));
    println!("Clipped topology:");
    print_topology_description(&clipped);
}
