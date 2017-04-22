mod dbf;
//mod shp;
//
//use std::io::{Error, Read};
//use dbf::DbfReader;
//use shp::ShpReader;
//
//#[derive(Debug)]
//struct Reader {
//    shp_reader: ShpReader,
//    dbf_reader: DbfReader,
//}
//
//impl Reader {
//    pub fn new(shp_file: &mut Read, dbf_file: &mut Read) -> Result<Reader, Error> {
//        match ShpReader::new(shp_file) {
//            Ok(shp_reader) => match DbfReader::new(dbf_file) {
//                Ok(dbf_reader) => {
//                    Ok(Reader {
//                        shp_reader: shp_reader,
//                        dbf_reader: dbf_reader,
//                    })
//                }
//                Error(err) => Error(err)
//            },
//            Error(err) => Error(err)
//        }
//    }
//}
