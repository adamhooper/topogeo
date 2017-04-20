use super::Point;
use itertools::Itertools;

/// A path joining two Points, via any number of intermediate Points.
#[derive(Clone,Debug)]
pub struct Edge(pub Vec<Point>);

/// A path joining a Point to itself, totalling three or more Points.
///
/// Clockwise means positive space (regions); counter-clockwise means negative
/// space (holes).
///
/// Beware self-intersecting Rings. Some algorithms require Rings not to
/// intersect themselves. We don't strictly enforce that rule, because
/// projecting a Ring into a new coordinate space can break the assumption.
#[derive(Clone,Debug)]
pub enum Ring {
    /// Efficient for geometry-related algorithms.
    Points(Vec<Point>),

    /// Efficient for topology-related algorithms.
    Edges(Vec<Edge>),
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum WindingOrder {
    Clockwise,
    CounterClockwise,
}

impl Ring {
    /// Returns all Points in the Ring, in order.
    pub fn points(&self) -> Vec<Point> {
        match self {
            &Ring::Points(ref points) => points.clone(),
            &Ring::Edges(ref edges) => {
                let len = edges.iter().fold(0, |sum, e| sum + e.0.len());
                let mut ret = Vec::<Point>::with_capacity(len);
                for edge in edges {
                    ret.extend_from_slice(&edge.0[.. edge.0.len() - 1]);
                }
                ret
            }
        }
    }

    /// Returns all Edges in the Ring, in order.
    pub fn edges(&self) -> Vec<Edge> {
        match self {
            &Ring::Edges(ref edges) => edges.clone(),
            &Ring::Points(ref points) => {
                points.windows(2).map(|e| Edge(e.to_vec())).collect()
            }
        }
    }

    /// Returns winding order.
    pub fn winding_order(&self) -> WindingOrder {
        let points = self.points();

        println!("{:?}", points);

        assert!(points.len() > 2);
        assert!(points.first() == points.last());

        // https://en.wikipedia.org/wiki/Shoelace_formula
        let mut a: i64 = 0;

        for (p1, p2) in points.iter().tuple_windows() {
            a += (p1.0 as i64) * (p2.1 as i64) - (p2.0 as i64) * (p1.1 as i64)
        }

        assert!(a != 0);
        if a > 0 {
            WindingOrder::Clockwise
        } else {
            WindingOrder::CounterClockwise
        }
    }
}

#[derive(Debug)]
pub struct Region<Data> {
    pub data: Data,
    pub outer_rings: Vec<Ring>,
    pub inner_rings: Vec<Ring>,
}

#[cfg(Test)]
mod test {
    #[test]
    fn test_edge_ring_edges() {
        let edges = vec![
            Edge(vec![ Point(1, 1), Point(1, 2), Point(2, 1) ]),
            Edge(vec![ Point(2, 1), Point(1, 1) ]),
        ];
        let ring: Ring = Ring::Edges(edges);
        assert_eq!(edges, ring.edges());
    }

    #[test]
    fn test_edge_ring_points() {
        let ring: Ring = Ring::Edges(vec![
            Edge(vec![ Point(1, 1), Point(1, 2), Point(2, 1) ]),
            Edge(vec![ Point(2, 1), Point(1, 1) ]),
        ]);
        assert_eq!(vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ], ring.points());
    }

    #[test]
    fn test_point_ring_edges() {
        let ring = Ring::Points(vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ]);
        assert_eq!(vec![
            Edge(vec! [ Point(1, 1), Point(1, 2) ]),
            Edge(vec! [ Point(1, 2), Point(2, 1) ]),
            Edge(vec! [ Point(2, 1), Point(1, 1) ]),
        ], ring.edges());
    }

    #[test]
    fn test_point_ring_points() {
        let points = vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ];
        let ring = Ring::Points(points);
        assert_eq!(points, ring.points());
    }
}
