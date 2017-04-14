use topogeo::topology::{DirectedEdge, Direction, Edge, InputEdge, InputRing, Point, Region, Ring, Topology, TopologyBuilder};

/// Edge data structure used when normalizing.
#[derive(Debug)]
struct NormEdge<T> {
    points: Vec<Point>,
    regions: Vec<*const Region<T>>,
}

impl<T> NormEdge<T> {
    fn with_directed_edge(directed_edge: &DirectedEdge<T>) -> NormEdge<T> {
        let ref edge: &Edge<_> = unsafe { &(*directed_edge.edge) };
        let mut mid_points = edge.mid_points.clone();

        let (n1, n2) = match directed_edge.direction {
            Direction::Forward => {
                (edge.node1, edge.node2)
            }
            Direction::Backward => {
                mid_points.reverse();
                (edge.node2, edge.node1)
            }
        };

        let p1 = unsafe { (*n1).point };
        let p2 = unsafe { (*n2).point };

        let mut points = Vec::<Point>::with_capacity(2 + mid_points.len());
        points.push(p1);
        points.append(&mut mid_points);
        points.push(p2);

        let regions: Vec<*const Region<T>> = edge.rings.iter().map(|&r| unsafe { (*r).region }).collect();

        NormEdge { points: points, regions: regions }
    }

    fn into_input_edge(self) -> InputEdge {
        InputEdge { points: self.points }
    }
}

impl<T> Clone for NormEdge<T> {
    fn clone(&self) -> NormEdge<T> {
        NormEdge {
            points: self.points.clone(),
            regions: self.regions.clone()
        }
    }
}

fn rotate_island_edge<T>(edge: &NormEdge<T>) -> NormEdge<T> {
    match edge.points.iter().enumerate().min_by_key(|&(_, p)| p) {
        None | Some((0, _)) => { NormEdge { points: edge.points.clone(), regions: edge.regions.clone() } },
        Some((index, _)) => {
            let mut points = Vec::<Point>::with_capacity(edge.points.len());
            points.extend_from_slice(&edge.points[index .. edge.points.len()]);
            points.extend_from_slice(&edge.points[0 .. index]);
            NormEdge { points: points, regions: edge.regions.clone() }
        }
    }
}

fn rotate_edges<T>(edges: &Vec<NormEdge<T>>) -> Vec<NormEdge<T>> {
    edges.clone().to_vec()
}

fn join_related_edges<T>(edges: &Vec<NormEdge<T>>) -> Vec<NormEdge<T>> {
    edges.clone().to_vec()
}

fn normalize_region_rings<T>(outer_rings: &[Box<Ring<T>>], inner_rings: &[Box<Ring<T>>]) -> (Vec<InputRing>, Vec<InputRing>) {
    let mut out_outer_rings = Vec::<InputRing>::with_capacity(outer_rings.len());
    let mut out_inner_rings = Vec::<InputRing>::with_capacity(inner_rings.len());

    for ref boxed_outer_ring in outer_rings {
        let ref outer_ring = *boxed_outer_ring;

        let mut edges = Vec::<InputEdge>::new();

        for ref directed_edge in &outer_ring.directed_edges {
            edges.push(NormEdge::<T>::with_directed_edge(directed_edge).into_input_edge());
        }

        out_outer_rings.push(InputRing { edges: edges });
    }

    (out_outer_rings, out_inner_rings)
}

/// Returns a "normalized" copy of the given Topology.
///
/// Normalization rules:
///
/// * **Fewest Rings possible**: A `Region` may not have two `Ring`s that share an `Edge`.
///   In other words: adjacent polygons must be merged.
/// * **Fewest Nodes and Edges possible**: No adjacent Edges may share the same Regions. In
///   other words: while all equivalent `Topology`s share the same `Point`s, a
///   *normalized* `Topology` has the most `mid_points` and the fewest `Node`s. An island
///   consists of a single *Edge*.
/// * **Ring direction**: Outer rings are clockwise; inner rings are counter-clockwise.
/// * **Left/Top-most ordering**: the first Edge in each Ring starts with the leftmost
///   (or in case of a tie, topmost) `Node`.
/// * **Island Node**: An island (or lake) has one Node, and that's the leftmost (or
///   in case of a tie, topmost) `Point`.
pub fn normalize<Data: Copy>(topo: &Topology<Data>) -> Topology<Data> {
    let mut builder = TopologyBuilder::<Data>::new();

    for ref region in &topo.regions {
        let (outer_rings, inner_rings) = normalize_region_rings(&region.outer_rings, &region.inner_rings);
        builder.add_region_with_rings(
            region.data,
            &outer_rings,
            &inner_rings,
        );
    }

    builder.into_topology()
}

#[cfg(test)]
mod test {
    use topogeo::topology::{Edge, Point, TopologyBuilder};
    use topogeo::normalize::normalize;

    #[test]
    fn flatten_ring() {
        let mut builder = TopologyBuilder::<()>::new();
        builder.add_region(
            (),
            &[ &[ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ] ],
            &[],
        );

        let topology = builder.into_topology();
        let normal = normalize(&topology);

        assert_eq!(1, normal.edges.len());
        let edge: &Edge<_> = normal.edges.keys().next().unwrap();
        assert_eq!(Point(1, 1), unsafe { (*edge.node1).point });
    }
}
