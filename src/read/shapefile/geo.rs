use std::io;
use geo;
use super::dbf;
use super::shp;
use super::shapefile;

#[derive(Debug)]
struct ShapefileQuantizer {
    pub x: f64,
    pub y: f64,
    pub w: f64,
    pub h: f64,
}

impl ShapefileQuantizer {
    fn new(bbox: &shp::ShpBoundingBox) -> ShapefileQuantizer {
        ShapefileQuantizer {
            x: bbox.0,
            y: bbox.3, // Assume (0,0) is bottom-left: that's what GIS programs do with WGS84
            w: bbox.2 - bbox.0,
            h: bbox.1 - bbox.3,
        }
    }

    fn quantize(&self, shp_point: &shp::ShpPoint) -> geo::Point {
        geo::Point(
            ((shp_point.0 - self.x) / self.w * u32::max_value() as f64) as u32,
            ((shp_point.1 - self.y) / self.h * u32::max_value() as f64) as u32,
        )
    }
}

#[derive(Debug)]
pub struct ShapefileGeoIterator<'a, T: io::Read+'a, U: io::Read+'a> {
    reader: &'a mut shapefile::ShapefileReader<T, U>,
    quantizer: ShapefileQuantizer,
}

impl<'a, T: io::Read+'a, U: io::Read+'a> ShapefileGeoIterator<'a, T, U> {
    pub fn new(reader: &'a mut shapefile::ShapefileReader<T, U>) -> ShapefileGeoIterator<T, U> {
        let quantizer = ShapefileQuantizer::new(reader.bounding_box());
        ShapefileGeoIterator {
            reader: reader,
            quantizer: quantizer,
        }
    }

    fn shp_polygon_ring_to_ring(&self, shp_ring: &shp::ShpPolygonRing) -> geo::Ring {
        let points: Vec<geo::Point> = shp_ring.0.iter().map(|p| self.quantizer.quantize(p)).collect();
        geo::Ring::Points(points.into_boxed_slice())
    }
}

impl<'a, T: io::Read, U: io::Read> Iterator for ShapefileGeoIterator<'a, T, U> {
    type Item = Result<geo::Region<dbf::DbfRecord>, shapefile::ShapefileError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.reader.next() {
            None => None,
            Some(Err(err)) => Some(Err(err)),
            Some(Ok(record)) => {
                let data = record.data;
                let (outer, inner): (Vec<_>, Vec<_>) = record.rings.into_iter()
                    .map(|r| self.shp_polygon_ring_to_ring(r))
                    .partition(|ring| ring.winding_order() == geo::WindingOrder::Clockwise);
                Some(Ok(geo::Region {
                    data: data,
                    outer_rings: outer.into_boxed_slice(),
                    inner_rings: inner.into_boxed_slice(),
                }))
            }
        }
    }
}

