use rust_dev skill.

clear clippy lints.

性能要求
- 减小类型体积
  - 32位不溢出就不用64位
  - 重复的信息只存一遍，不冗余，包括非常容易重新计算的。
  - 不允许存未经压缩的Vec<enum>、Vec<Option<T>>等。
    - 不管你具体怎么压，反正需要0 padding。
- 不允许使用Arc和Rc。
- 减少分配
  - 循环里复用缓冲区
  - 考虑在更长生命周期之间复用分配
  - 不允许返回短命的Box<[T]>，Vec<T>，String。

文档要求
- rustdoc要详细，包括 private item。启用有关lint