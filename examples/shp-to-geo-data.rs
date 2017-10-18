extern crate topogeo;

use std::env;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process;
use topogeo::read::shapefile;
use topogeo::topology;
use topogeo::clip;
use topogeo::geo;

fn print_topology_description<Data>(topology: &topology::Topology<Data>) {
    let mut n_outer_rings = 0;
    let mut n_inner_rings = 0;

    for ref region in topology.regions.iter() {
        n_outer_rings += region.outer_ring_ids.len();
        n_inner_rings += region.inner_ring_ids.len();
    }

    let mut n_shared_edges = 0;
    let mut n_lone_edges = 0;
    let mut n_points = 0;

    for edge in topology.edges.iter() {
        if edge.ring2_id == topology::NULL_ID {
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

    let regions: Vec<geo::Region<shapefile::DbfRecord>> = match shapefile::open_windows1252(&path) {
        Err(err) => {
            writeln!(&mut io::stderr(), "{}", err).unwrap();
            process::exit(1);
        }
        Ok(mut reader) => {
            let mut regions: Vec<geo::Region<shapefile::DbfRecord>> = vec!();

            for region_result in shapefile::ShapefileGeoIterator::new(&mut reader) {
                match region_result {
                    Err(err) => {
                        writeln!(&mut io::stderr(), "Error during read: {}", err).unwrap();
                        process::exit(1);
                    }
                    Ok(region) => {
                        regions.push(region);
                    }
                }
            }

            regions
        }
    };

    println!("Read {} regions", regions.len());

    let clip_mask = clip::ClipMask::MinX(1u32 << 31);
    let clipped_regions: Vec<_> = regions
        .into_iter()
        .map(|region| clip::clip_region(region, &clip_mask))
        .filter(|region| region.outer_rings.len() > 0)
        .collect();
    println!("Clipped topology, so now there are {} regions", clipped_regions.len());

    let clip_mask2 = clip::ClipMask::MinY(1u32 << 31);
    let clipped_regions2: Vec<_> = clipped_regions
        .into_iter()
        .map(|region| clip::clip_region(region, &clip_mask2))
        .filter(|region| region.outer_rings.len() > 0)
        .collect();
    println!("Clipped again, so now there are {} regions", clipped_regions2.len());

    let mut builder = topology::TopologyBuilder::new();
    for region in clipped_regions2 { builder.add_region(region) }
    let topology = builder.into_topology();
    println!("Formed initial topology:");
    print_topology_description(&topology);

    let normalized = topogeo::normalize(&topology);
    println!("Normalized topology:");
    print_topology_description(&normalized);
}
