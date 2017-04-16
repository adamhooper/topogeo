use topogeo::Point;
use itertools::Itertools;

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum WindingOrder {
    Clockwise,
    CounterClockwise,
}


pub fn calculate_winding_order_from_points(points: &[Point]) -> WindingOrder {
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
