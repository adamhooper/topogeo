use geo::{Point, Rectangle, Region, Ring, WindingOrder};
use clip::types::{ClipLocation, ClipMask};
use itertools::Itertools;

fn points_to_bounds(points: &[Point]) -> Rectangle {
    let mut left = u32::max_value();
    let mut right = u32::min_value();
    let mut top = u32::max_value();
    let mut bottom = u32::min_value();

    for point in points.iter() {
        if point.0 < left { left = point.0; }
        if point.0 > right { right = point.0; }
        if point.1 < top { top = point.1; }
        if point.1 > bottom { bottom = point.1; }
    }

    Rectangle {
        left: left,
        right: right,
        top: top,
        bottom: bottom,
    }
}

#[derive(Debug,Eq,PartialEq)]
struct UnprocessedRings {
    fully_within_mask: Vec<Ring>,
    partially_within_mask: Vec<Ring>,
}

/// Partitions rings into fully-inside and need-to-be-clipped collections;
/// nixes fully-outside rings.
///
/// One big simplification may be confusing: at this point, outer rings and
/// their holes aren't associated. So we may mark an outer ring as
/// `partially_within_mask` while marking its holes as `fully_within_mask`: that
/// would lead us to clip the outer ring but not its holes. That's actually a
/// _good_ thing: we needn't associate that hole with its ring, ever, because
/// the output Region won't need it. We'll just copy the holes into the final
/// output.
///
/// We assume an outer ring surrounds its holes: if a hole is
/// `partially_within_mask`, it follows that its outer ring is
/// `partially_within_mask`.
fn find_unprocessed_rings(rings: &[Ring], mask: &ClipMask) -> UnprocessedRings {
    let mut fully_within_mask = Vec::<Ring>::new();
    let mut partially_within_mask = Vec::<Ring>::new();

    for ring in rings {
        let mut all_inside = true;
        let mut all_outside = true;

        for point in ring.points().iter() {
            match mask.test(point) {
                ClipLocation::Inside => { all_outside = false; }
                ClipLocation::Outside => { all_inside = false; }
                ClipLocation::OnEdge => {}
            }
        }

        if all_inside {
            fully_within_mask.push(ring.clone());
        } else if !all_outside {
            partially_within_mask.push(ring.clone());
        }
    }

    UnprocessedRings {
        fully_within_mask: fully_within_mask,
        partially_within_mask: partially_within_mask,
    }
}

/// Undefined behavior if the point is _on_ the ring.
fn ring_contains_point(ring: &[Point], point: Point) -> bool {
    fn x(p: Point) -> i64 { p.0 as i64 }
    fn y(p: Point) -> i64 { p.1 as i64 }

    // http://geomalgorithms.com/a03-_inclusion.html
    //    Input:  three points P0, P1, and P2
    //    Return: >0 for P2 left of the line through P0 and P1
    //            =0 for P2  on the line
    //            <0 for P2  right of the line
    fn is_left(p0: Point, p1: Point, p2: Point) -> i64 {
        (x(p1) - x(p0)) * (y(p2) - y(p0)) - (x(p2) - x(p0)) * (y(p1) - y(p0))
    }

    let mut wn = 0; // 0 means "outside polygon"; non-0 means inside

    // here, "p1" and "p2" mean something completely different from in the
    // above helper functions
    for (&p1, &p2) in ring.iter().tuple_windows() { // edge p1-p2
        if p1.1 <= point.1 {
            if p2.1 > point.1 { // an upward crossing
                if is_left(p1, p2, point) > 0 {
                    wn += 1; // valid up intersect
                }
            }
        } else {
            if p2.1 <= point.1 { // a downward crossing
                if is_left(p1, p2, point) < 0 {
                    wn -= 1; // valid down intersect
                }
            }
        }
    }

    wn != 0
}

/// An outer contour in clockwise direction, plus opposite-direction holes
/// within that outer contour.
#[derive(Debug,Eq,PartialEq)]
struct Polygon {
    main_contour: Vec<Point>,
    hole_contours: Vec<Vec<Point>>,
}

fn ring_contains_hole(ring: &[Point], ring_bounds: &Rectangle, hole: &[Point], hole_bounds: &Rectangle) -> bool {
    if hole_bounds.top > ring_bounds.top && hole_bounds.bottom < ring_bounds.bottom && hole_bounds.left > ring_bounds.left && hole_bounds.right < ring_bounds.right {
        ring_contains_point(ring, hole[0])
    } else {
        // If the hole is not strictly inside the ring then we know right away
        // it can't be inside
        false
    }
}

fn rings_to_polygons<I>(outer_rings: I, inner_rings: I) -> Vec<Polygon>
    where I: IntoIterator<Item=Ring>
{
    struct PolygonBuilder {
        main_contour: Vec<Point>,
        area2: u64,
        bounds: Rectangle,
        hole_contours: Vec<Vec<Point>>,
    }

    let mut polygon_builders: Vec<PolygonBuilder> = outer_rings.into_iter()
        .map(|ring| {
            let mut main_contour = ring.points().to_vec();
            let (area2, winding_order) = ring.area2_and_winding_order();
            if winding_order == WindingOrder::CounterClockwise {
                main_contour.reverse();
            }
            let bounds = points_to_bounds(&main_contour[..]);

            PolygonBuilder {
                main_contour: main_contour,
                area2: area2,
                bounds: bounds,
                hole_contours: vec![],
            }
        })
        .collect();

    // Put smallest polygons in front. That will help with this case:
    //
    // +------------+
    // |A           |
    // | +--------+ |
    // | |////////| |
    // | |/+----+/| |
    // | |/|B   |/| |
    // | |/| ++ |/| |
    // | |/| ++ |/| |
    // | |/|    |/| |
    // | |/+----+/| |
    // | |////////| |
    // | +--------+ |
    // |            |
    // +------------+
    //
    // That is, polygon A has a hole, and polygon B has a hole, and B is within
    // A's hole.
    //
    // A's hole should be paired with A when clipping, and B's hole should be
    // paired with B. When B is clipped, A will be clipped as well; A-prime
    // (post-clip) won't have a hole after the clip. (B-prime might.)
    //
    // To pair holes with the innermost polygons, test whether a hole is within
    // the innermost polygon before testing the outer one. Sort-by-area makes
    // this easy.
    polygon_builders.sort_by_key(|a| a.area2);

    'inner_ring: for inner_ring in inner_rings.into_iter() {
        let mut hole_contour = inner_ring.points().to_vec();
        if inner_ring.winding_order() == WindingOrder::Clockwise {
            hole_contour.reverse();
        }
        let hole_bounds = points_to_bounds(&hole_contour[..]);

        for mut polygon_builder in polygon_builders.iter_mut() {
            if ring_contains_hole(&polygon_builder.main_contour[..], &polygon_builder.bounds, &hole_contour[..], &hole_bounds) {
                polygon_builder.hole_contours.push(hole_contour);
                continue 'inner_ring;
            }
        }

        unreachable!("Inner ring {:?} is not contained in any outer ring", inner_ring);
    }

    polygon_builders.into_iter()
        .map(|pb| Polygon {
            main_contour: pb.main_contour,
            hole_contours: pb.hole_contours,
        })
        .collect()
}

/// Crop the given Polygon, producing new outer rings.
///
/// This uses the [Weiler–Atherton clipping
/// algorithm](https://en.wikipedia.org/wiki/Weiler%E2%80%93Atherton_clipping_algorithm),
/// with simplifications:
///
/// * We assume all the polygon's rings straddle the clip mask. When we clip,
///   we'll produce one or more outer rings and _zero_ holes: each of the input
///   holes will become part of the output outer rings, and there's no way to
///   produce a new hole because the clip mask is a rectangle.
///   (TODO: better proof?)
fn clip_polygon(_polygon: Polygon, _mask: &ClipMask) -> Vec<Ring> {
    vec![]
}

/// Clips a Region so that all Points are inside the given ClipMask.
///
/// This uses the [Weiler–Atherton clipping
/// algorithm](https://en.wikipedia.org/wiki/Weiler%E2%80%93Atherton_clipping_algorithm),
/// somewhat simplified to only support bisection.
pub fn clip_region<Data>(region: Region<Data>, mask: &ClipMask) -> Region<Data> {
    let Region { data, outer_rings, inner_rings } = region;

    let (mut fast_outer_rings, slow_outer_rings): (Vec<Ring>, Vec<Ring>) = {
        let t = find_unprocessed_rings(&outer_rings[..], mask);
        (t.fully_within_mask, t.partially_within_mask)
    };

    let (fast_inner_rings, slow_inner_rings): (Vec<Ring>, Vec<Ring>) = {
        let t = find_unprocessed_rings(&inner_rings[..], mask);
        (t.fully_within_mask, t.partially_within_mask)
    };

    let polygons = rings_to_polygons(slow_outer_rings, slow_inner_rings);
    let mut outer_rings: Vec<Ring> = polygons.into_iter().flat_map(|p| clip_polygon(p, mask)).collect();
    outer_rings.append(&mut fast_outer_rings);

    Region {
        data: data,
        outer_rings: outer_rings.into_boxed_slice(),
        inner_rings: fast_inner_rings.into_boxed_slice(),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn typical_points_to_bounds() {
        assert_eq!(
            Rectangle { left: 2, right: 4, top: 1, bottom: 10 },
            points_to_bounds(&vec![ Point(3, 1), Point(4, 5), Point(2, 10) ])
        );
    }

    #[test]
    fn find_unprocessed_rings_nix_outside_ring() {
        let ring = Ring::Points(vec![ Point(0, 0), Point(1, 0), Point(0, 1), Point(0, 0) ].into_boxed_slice());

        assert_eq!(
            UnprocessedRings { fully_within_mask: vec![], partially_within_mask: vec![] },
            find_unprocessed_rings(&vec![ ring ], &ClipMask::MinX(1))
        );
    }

    #[test]
    fn find_unprocessed_rings_fully_within_mask() {
        let ring = Ring::Points(vec![ Point(0, 0), Point(1, 0), Point(0, 1), Point(0, 0) ].into_boxed_slice());

        assert_eq!(
            UnprocessedRings { fully_within_mask: vec![ ring.clone() ], partially_within_mask: vec![] },
            find_unprocessed_rings(&vec![ ring ], &ClipMask::MaxX(1))
        );
    }

    #[test]
    fn find_unprocessed_rings_partially_within_mask() {
        let ring = Ring::Points(vec![ Point(0, 0), Point(2, 0), Point(0, 1), Point(0, 0) ].into_boxed_slice());

        assert_eq!(
            UnprocessedRings { fully_within_mask: vec![], partially_within_mask: vec![ ring.clone() ] },
            find_unprocessed_rings(&vec![ ring ], &ClipMask::MaxX(1))
        );
    }

    #[test]
    fn ring_contains_point_typical() {
        assert!(
            ring_contains_point(&vec![ Point(0, 0), Point(3, 0), Point(0, 3), Point(0, 0) ], Point(1, 1))
        );
    }

    #[test]
    fn ring_contains_hole_typical() {
        assert!(ring_contains_hole(
            &vec![ Point(0, 0), Point(4, 0), Point(0, 4), Point(0, 0) ],
            &Rectangle { top: 0, bottom: 4, left: 0, right: 4 },
            &vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
            &Rectangle { top: 1, bottom: 2, left: 1, right: 2 },
        ));
    }

    #[test]
    fn ring_contains_hole_disjoint_bounds() {
        assert!(!ring_contains_hole(
            &vec![ Point(0, 0), Point(3, 0), Point(0, 3), Point(0, 0) ],
            &Rectangle { top: 0, bottom: 3, left: 0, right: 3 },
            &vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ],
            &Rectangle { top: 3, bottom: 4, left: 1, right: 2 },
        ));
    }

    #[test]
    fn ring_contains_hole_outside_gives_false() {
        // +---+
        // |  /
        // | /+
        // |/++
        // +
        assert!(!ring_contains_hole(
            &vec![ Point(0, 0), Point(4, 0), Point(0, 4), Point(0, 0) ],
            &Rectangle { top: 0, bottom: 3, left: 0, right: 3 },
            &vec![ Point(2, 3), Point(3, 2), Point(3, 3), Point(2, 3) ],
            &Rectangle { top: 1, bottom: 2, left: 1, right: 2 },
        ));
    }

    #[test]
    fn ring_to_polygons_typical() {
        let outer1 = vec![ Point(0, 0), Point(4, 0), Point(0, 4), Point(0, 0) ];
        let outer2 = vec![ Point(5, 0), Point(9, 0), Point(5, 4), Point(5, 0) ];
        let inner1 = vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ];
        let inner2 = vec![ Point(6, 1), Point(6, 2), Point(7, 1), Point(6, 1) ];

        assert_eq!(
            vec![
                Polygon { main_contour: outer1.clone(), hole_contours: vec![ inner1.clone() ] },
                Polygon { main_contour: outer2.clone(), hole_contours: vec![ inner2.clone() ] },
            ],
            rings_to_polygons(
                vec![ Ring::Points(outer1.into_boxed_slice()), Ring::Points(outer2.into_boxed_slice()) ],
                vec![ Ring::Points(inner2.into_boxed_slice()), Ring::Points(inner1.into_boxed_slice()) ]
            )
        );
    }

    #[test]
    fn ring_to_polygons_donuts() {
        // +------------+
        // |A           |
        // | +--------+ |
        // | |////////| |
        // | |/+----+/| |
        // | |/|B   |/| |
        // | |/| ++ |/| |
        // | |/| ++ |/| |
        // | |/|    |/| |
        // | |/+----+/| |
        // | |////////| |
        // | +--------+ |
        // |            |
        // +------------+
        //
        // Even though B's hole is inside A, it should only be associated with B
        let a_ring = vec![ Point(0, 0), Point(7, 0), Point(7, 7), Point(0, 7), Point(0, 0) ];
        let a_hole = vec![ Point(1, 1), Point(1, 6), Point(6, 6), Point(6, 1), Point(1, 1) ];
        let b_ring = vec![ Point(2, 2), Point(5, 2), Point(5, 5), Point(2, 5), Point(2, 2) ];
        let b_hole = vec![ Point(3, 3), Point(3, 4), Point(4, 4), Point(4, 3), Point(3, 3) ];

        assert_eq!(
            vec![
                Polygon { main_contour: b_ring.clone(), hole_contours: vec![ b_hole.clone() ] },
                Polygon { main_contour: a_ring.clone(), hole_contours: vec![ a_hole.clone() ] },
            ],
            rings_to_polygons(
                vec![ Ring::Points(a_ring.into_boxed_slice()), Ring::Points(b_ring.into_boxed_slice()) ],
                vec![ Ring::Points(a_hole.into_boxed_slice()), Ring::Points(b_hole.into_boxed_slice()) ]
            )
        );
    }

    #[test]
    fn ring_to_polygons_rings_clockwise() {
        let cw = vec![ Point(0, 0), Point(4, 0), Point(0, 4), Point(0, 0) ];
        let ccw = vec![ Point(0, 0), Point(0, 4), Point(4, 0), Point(0, 0) ];

        assert_eq!(
            vec![ Polygon { main_contour: cw.clone(), hole_contours: vec![] } ],
            rings_to_polygons(vec![ Ring::Points(ccw.into_boxed_slice()) ], vec![])
        );
    }

    #[test]
    fn ring_to_polygons_holes_counterclockwise() {
        let outer = vec![ Point(0, 0), Point(4, 0), Point(0, 4), Point(0, 0) ];
        let inner_cw = vec![ Point(1, 1), Point(2, 1), Point(1, 2), Point(1, 1) ];
        let inner_ccw = vec![ Point(1, 1), Point(1, 2), Point(2, 1), Point(1, 1) ];

        assert_eq!(
            vec![ Polygon { main_contour: outer.clone(), hole_contours: vec![ inner_ccw.clone() ] } ],
            rings_to_polygons(
                vec![ Ring::Points(outer.into_boxed_slice()) ],
                vec![ Ring::Points(inner_cw.into_boxed_slice()) ]
            )
        );
    }
}
