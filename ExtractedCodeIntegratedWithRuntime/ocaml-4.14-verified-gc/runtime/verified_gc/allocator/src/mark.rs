use crate::{
    colors::{BLACK, GRAY, WHITE},
    utils::field_val,
    value::Value,
};

pub struct Marker {
    pub stack: Vec<Value>,
}

impl Marker {
    pub fn new(size_hint: Option<usize>) -> Marker {
        Marker {
            stack: Vec::with_capacity(size_hint.unwrap_or_default()),
        }
    }

    fn push_fields_to_stack_and_color_black(&mut self, val: Value) {
        val.get_header().set_color(BLACK);
        let wosz = *val.get_header().get_wosize().get_val();
        for i in 0..wosz {
            let field_at_offset = unsafe { Value(*{ field_val(val, i as isize).0 as *mut usize }) };
            if field_at_offset.is_ptr() && field_at_offset.get_header().get_color() == WHITE {
                field_at_offset.get_header().set_color(GRAY);
                self.stack.push(field_at_offset);
            }
        }
    }

    pub fn mark(&mut self, val: Value) {
        assert!(self.stack.is_empty());
        val.get_header().set_color(GRAY);
        self.stack.push(val);
        while !self.stack.is_empty() {
            let last = self.stack.pop().unwrap();
            assert_eq!(last.get_header().get_color(), GRAY);
            self.push_fields_to_stack_and_color_black(last);
        }
        assert!(self.stack.is_empty());
    }
}
