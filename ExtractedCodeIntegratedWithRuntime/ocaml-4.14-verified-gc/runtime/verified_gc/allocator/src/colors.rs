pub type Color = usize;

/* #define Caml_white (0 << 8) */
/* #define Caml_gray  (1 << 8) */
/* #define Caml_blue  (2 << 8) */
/* #define Caml_black (3 << 8) */
pub const WHITE: Color = 0usize << 8;
pub const GRAY: Color = 1usize << 8;
pub const BLUE: Color = 2usize << 8;
pub const BLACK: Color = 3usize << 8;
