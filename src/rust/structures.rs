#[derive(Debug, PartialEq, Eq)]
pub(crate) struct VtableHeader {
    pub drop: Option<u64>,
    pub size: u64,
    pub alignment: u64,
    pub first_method: u64,
}

/// A plausible header, without assuming the number or kinds of later slots.
pub(crate) fn vtable(words: [u64; 4], executable: impl Fn(u64) -> bool) -> Option<VtableHeader> {
    let [drop, size, alignment, first_method] = words;
    if size > 1 << 20
        || alignment == 0
        || alignment > 256
        || !alignment.is_power_of_two()
        || size % alignment != 0
        || (drop != 0 && !executable(drop))
        || !executable(first_method)
    {
        return None;
    }
    Some(VtableHeader {
        drop: (drop != 0).then_some(drop),
        size,
        alignment,
        first_method,
    })
}

pub(crate) fn text(bytes: &[u8]) -> Option<&str> {
    let text = std::str::from_utf8(bytes).ok()?;
    text.chars()
        .all(|character| !character.is_control() || matches!(character, '\n' | '\r' | '\t'))
        .then_some(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nullable_drop_and_a_single_method_are_sufficient_for_a_candidate() {
        let header = vtable([0, 24, 8, 0x4000], |address| address == 0x4000).unwrap();
        assert_eq!(header.drop, None);
        assert_eq!(header.first_method, 0x4000);
    }

    #[test]
    fn reject_noncode_and_inconsistent_layouts() {
        assert!(vtable([0, 24, 3, 0x4000], |_| true).is_none());
        assert!(vtable([0, 23, 8, 0x4000], |_| true).is_none());
        assert!(vtable([0x5000, 24, 8, 0x4000], |address| address == 0x4000).is_none());
        assert!(vtable([0, 24, 8, 0x4000], |_| false).is_none());
    }

    #[test]
    fn text_detection_does_not_require_a_terminator() {
        assert_eq!(text(b"hello\nworld"), Some("hello\nworld"));
        assert_eq!(text(&[0xff]), None);
        assert_eq!(text(b"binary\0data"), None);
    }
}
