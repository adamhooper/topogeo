extern crate byteorder;
extern crate encoding;
extern crate itertools;
#[macro_use] extern crate lazy_static;
extern crate regex;

pub mod clip;
pub mod geo;
pub mod topology;
pub mod read;

mod normalize;
mod simplify;

pub use normalize::normalize;
pub use simplify::simplify;
