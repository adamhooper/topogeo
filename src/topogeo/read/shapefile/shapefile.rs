pub struct Reader {
    shp: &mut Read,
    dbf: &mut Read,
}

impl Reader {
    pub fn next_region(&mut self) -> Result<Region<DbfRecord>> {
        self.shp.Seek(shp_offset);
        self.dbf.Seek(dbf_offset);
    }
}

pub fn read(shp: &mut Read, dbf: &mut Read, 
