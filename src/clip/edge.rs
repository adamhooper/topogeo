use geo::Point;

use clip::types::{ClipLocation, ClipMask};

/// Clips an edge so that only the part the mask includes is returned.
///
/// # Examples
///
/// ```
/// use topogeo::clip::ClipMask;
/// use topogeo::clip::edge::clip_edge;
/// use topogeo::geo::Point;
///
/// //   .
/// // *-.--*
/// //   . /
/// //   ./
/// //   .
/// //  /.
/// // *-.--*
/// //   . /
/// //   ./
/// //   .
/// //   .
/// //  /.
/// // *-.--*
/// //   ^ clipped here, only accepting the right side
/// let clipped = clip_edge(&[
///     Point(10, 10), Point(50, 10), Point(10, 50),
///     Point(50, 50), Point(10, 100), Point(50, 100),
/// ], &ClipMask::MinX(20));
///
/// assert_eq!(vec![
///   Point(20, 10), Point(50, 10), Point(20, 40), Point(20, 50),
///   Point(50, 50), Point(20, 87), Point(20, 100), Point(50, 100),
/// ], clipped.to_vec());
/// ```
pub fn clip_edge(points: &[Point], mask: &ClipMask) -> Box<[Point]> {
    // https://en.wikipedia.org/wiki/Sutherland%E2%80%93Hodgman_algorithm
    if points.len() < 2 {
        return vec![].into_boxed_slice()
    }

    let mut ret = Vec::<Point>::with_capacity(points.len() * 2);

    let mut previous_point: &Point = &points[0];
    let mut previous_location = mask.test(previous_point);
    if previous_location == ClipLocation::Inside {
        ret.push(*previous_point);
    }

    for point in &points[1 .. ] {
        let location = mask.test(point);

        match location {
            ClipLocation::OnEdge => {
                // If we got to this edge from:
                // outside => we're still on the outside
                // inside => this is a legit line
                // edge => eventually we'll either head inside or outside.
                //         only draw a line when we do.
                if previous_location == ClipLocation::Inside {
                    ret.push(*point);
                }
            }
            ClipLocation::Inside => {
                if previous_location == ClipLocation::Outside {
                    ret.push(mask.intersect(previous_point, point));
                }

                if previous_location == ClipLocation::OnEdge {
                    // We've been along the edge for any number of points.
                    if ret.last() != Some(previous_point) {
                        ret.push(*previous_point);
                    }
                }

                ret.push(*point);
            }
            ClipLocation::Outside => {
                if previous_location == ClipLocation::Inside {
                    ret.push(mask.intersect(previous_point, point));
                }
            }
        }

        previous_point = point;
        previous_location = location;
    }

    ret.into_boxed_slice()
}

#[cfg(test)]
mod test {
    use geo::Point;
    use clip::types::ClipMask;
    use super::clip_edge;

    #[test]
    fn len_0_empty() {
        assert_eq!(Vec::<Point>::new(), clip_edge(&[], &ClipMask::MaxX(2)).to_vec());
    }

    #[test]
    fn len_1_empty() {
        assert_eq!(Vec::<Point>::new(), clip_edge(&[ Point(1, 1) ], &ClipMask::MaxX(2)).to_vec());
    }

    #[test]
    fn unchanged() {
        assert_eq!(
            vec![ Point(1, 1), Point(2, 2), Point(1, 2) ],
            clip_edge(&[ Point(1, 1), Point(2, 2), Point(1, 2) ], &ClipMask::MaxX(2)).to_vec()
        );
    }

    #[test]
    fn cross_out_on_point() {
        assert_eq!(
            vec![ Point(1, 1), Point(2, 2) ],
            clip_edge(&[ Point(1, 1), Point(2, 2), Point(3, 2) ], &ClipMask::MaxX(2)).to_vec()
        );
    }

    #[test]
    fn cross_out_interpolate() {
        assert_eq!(
            vec![ Point(1, 1), Point(2, 2) ],
            clip_edge(&[ Point(1, 1), Point(3, 3), Point(4, 3) ], &ClipMask::MaxX(2)).to_vec()
        );
    }

    #[test]
    fn cross_in_on_point() {
        assert_eq!(
            vec![ Point(2, 2), Point(3, 3) ],
            clip_edge(&[ Point(0, 1), Point(2, 2), Point(3, 3) ], &ClipMask::MinX(2)).to_vec()
        );
    }

    #[test]
    fn cross_in_interpolate() {
        assert_eq!(
            vec![ Point(2, 2), Point(3, 3) ],
            clip_edge(&[ Point(0, 1), Point(1, 1), Point(3, 3) ], &ClipMask::MinX(2)).to_vec()
        );
    }

    #[test]
    fn flush_edge_out() {
        assert_eq!(
            Vec::<Point>::new(),
            clip_edge(&[ Point(1, 1), Point(2, 1), Point(2, 2), Point(1, 1) ], &ClipMask::MinX(2)).to_vec()
        );
    }

    #[test]
    fn flush_edge_in() {
        let ring = vec![ Point(1, 1), Point(2, 1), Point(2, 2), Point(1, 1) ];
        assert_eq!(ring, clip_edge(&ring[..], &ClipMask::MaxX(2)).to_vec());
    }
}
