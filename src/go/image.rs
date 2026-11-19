use binaryninja::binary_view::{BinaryView, BinaryViewBase};
use sha2::{Digest, Sha256};
use unstrip::GoBinary;

/// Parse a snapshot of the current view, including unsaved byte edits.
pub(crate) struct Image {
    pub binary: GoBinary,
    slide: i128,
}

impl Image {
    pub fn fingerprint(&self) -> String {
        let mut hash = Sha256::new();
        hash.update(self.slide.to_le_bytes());
        hash.update(&self.binary.bytes);
        format!("{:x}", hash.finalize())
    }

    pub fn read(view: &BinaryView) -> Result<Self, String> {
        let raw = view
            .raw_view()
            .ok_or("view has no executable backing data")?;
        let size = usize::try_from(raw.len()).map_err(|_| "executable is too large")?;
        let mut binary =
            GoBinary::parse(raw.read_vec(raw.start(), size)).map_err(|error| error.to_string())?;
        let slide = i128::from(view.image_base()) - i128::from(view.original_image_base());
        for section in &binary.sections {
            if section.file_size == 0 {
                continue;
            }
            let loaded = Self::translate(section.addr, slide).ok_or("section address overflow")?;
            if !view.offset_valid(loaded) {
                continue;
            }
            let bytes = view.read_vec(loaded, section.file_size);
            if bytes.len() != section.file_size {
                return Err(format!("section {} is not fully mapped", section.name));
            }
            let end = section
                .file_offset
                .checked_add(bytes.len())
                .ok_or("section extent overflow")?;
            binary
                .bytes
                .get_mut(section.file_offset..end)
                .ok_or("section exceeds executable backing data")?
                .copy_from_slice(&bytes);
        }
        Ok(Self { binary, slide })
    }

    fn translate(address: u64, slide: i128) -> Option<u64> {
        u64::try_from(i128::from(address) + slide).ok()
    }

    pub fn loaded_address(&self, address: u64) -> Option<u64> {
        Self::translate(address, self.slide)
    }

    pub fn original_address(&self, address: u64) -> Option<u64> {
        Self::translate(address, -self.slide)
    }
}

#[cfg(test)]
mod tests {
    use super::Image;

    #[test]
    fn addresses_support_both_slide_directions_without_wrapping() {
        assert_eq!(Image::translate(0x4000, -0x1000), Some(0x3000));
        assert_eq!(Image::translate(0x4000, 0x1000), Some(0x5000));
        assert_eq!(Image::translate(0, -1), None);
        assert_eq!(Image::translate(u64::MAX, 1), None);
    }
}
