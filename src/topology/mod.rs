mod types;
mod build;

pub use self::types::{Topology, TopoEdge, TopoRegion, TopoRing, DirectedEdge, Direction};
pub use self::build::TopologyBuilder;
