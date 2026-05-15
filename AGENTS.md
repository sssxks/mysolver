use rust_dev skill for design guidance.

clear clippy lints.

文档要求
- rustdoc要详细，包括 private item。启用 `missing_docs` 和 `missing_docs_in_private_items` lint，对着修即可。这个workspace已启用，不需要再加`#![warn(missing_docs, clippy::missing_docs_in_private_items)]`了。