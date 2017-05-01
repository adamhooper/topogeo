//! Returns a Topology that may be simpler than the given one.
use super::topology;
mod simplify_edge;

pub fn simplify<Data>(mut topology: topology::Topology<Data>, smallest_area: u64) -> topology::Topology<Data> {
    for ref mut edge in topology.edges.iter_mut() {
        let new_points = simplify_edge::simplify_edge(&edge.points[..], smallest_area);
        edge.points = new_points;
    }
    topology
}
