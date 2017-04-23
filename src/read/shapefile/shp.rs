use std::io::{Error, Read, Seek};

pub struct ShpReader<'a> {
    file: &'a Read,
    header: ShpHeader,
}
