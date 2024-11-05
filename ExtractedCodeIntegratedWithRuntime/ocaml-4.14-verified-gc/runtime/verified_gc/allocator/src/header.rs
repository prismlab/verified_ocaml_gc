use std::fmt::{self, Debug};

use crate::{
    colors::{Color, BLACK, BLUE, GRAY, WHITE},
    word::Wsize,
};

#[repr(transparent)]
#[derive(Clone)]
pub struct Header(usize);

impl Header {
    pub const fn new(size: usize, color: Color, tag: u8) -> Header {
        Header((size << 10) + color + (tag as usize))
    }
    pub fn get_tag(&self) -> u8 {
        (self.0 & 0xff) as u8
    }
    pub fn get_color(&self) -> Color {
        self.0 & 0b1100000000
    }
    pub fn get_wosize(&self) -> Wsize {
        Wsize::new(self.0 >> 10)
    }
    pub fn to_usize(&self) -> usize {
        self.0
    }
    pub fn set_color(&mut self, color: Color) {
        self.0 = ((usize::max_value() ^ 0b1100000000) & self.0) | color;
    }
    pub fn set_wosize(&mut self, new_sz: Wsize) {
        let sz_as_usize = *new_sz.get_val();
        self.0 = (self.0 & 0b1111111111) | (sz_as_usize << 10)
    }
    pub fn set_tag(&mut self, tag: u8) {
        self.0 = (self.0 ^ (self.0 & 0xff)) | (tag as usize);
    }
}

impl Debug for Header {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Header")
            .field("size", &self.get_wosize())
            .field("color", {
                match self.get_color() {
                    BLUE => &"Blue",
                    GRAY => &"Gray",
                    BLACK => &"Black",
                    WHITE => &"White",
                    _ => &"Unknown",
                }
            })
            .field("tag", &self.get_tag())
            .finish()
    }
}

#[cfg(test)]
mod header_tests {

    use crate::colors::BLUE;

    use super::Header;

    #[test]
    fn test() {
        let hd = Header::new(10, BLUE, 255);
        assert_eq!(*hd.get_wosize().get_val(), 10);
        assert_eq!(hd.get_color(), BLUE);
        assert_eq!(hd.get_tag(), 255);
    }
}
