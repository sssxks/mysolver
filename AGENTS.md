use rust_dev skill.

clear clippy lints.

性能要求
- 减小类型体积
  - 32 位整数不溢出，就不用 64 位整数
    - 可考虑 16 位，如果可用。
    - 可考虑切分一个大的 32 / 64 位整数为多个部分，使每个部分都有恰当的表达范围。
  - 重复的信息只存一遍，不冗余
    - O(1) 时间可重新计算的信息也算冗余。
    - 只保留必要的索引结构等。
  - 不存未经压缩的 Vec<enum>、Vec<Option<T>> 等带有显著 padding 的类型。
    - 使用恰当的压缩，让内存布局 0 padding。
      - 使用 BitVec 等，或者手写 niche。
      - SoA 不要每个field分配一个Vec， Vec<field1> * Vec<field2> * ...。事实上这些Vec都是同步扩容的，可以合并为一个 Vec<u8>，并自行解释为 SoA。
      - 更多合适的做法等。
    - 构建恰当的抽象，不牺牲可读性。解决方案不能太 ad-hoc。
      - 文档说明这个类型对应的简单版语义版类型。
- 不使用 Rc。
  - 单线程程序不使用Arc，只用于跨线程共享不可变数据。
- 减少分配
  - 循环里复用缓冲区
  - 考虑在更长生命周期之间复用分配
    - 当然也要考虑 clear 的开销。
  - 不允许返回不必要的堆分配，比如 Vec<T>，String 等。函数不应当强制调用者承担分配负担。
    - `impl Iterator`, `&mut` 入参等
- 减少 indirection。
  - 有时 inline 既能减少指针跳转又不增加体积，那就应该 inline。
  - 如果我们已经达到了 inline v.s. indirection 的帕累托最优，才考虑 inline v.s. indirection 权衡。
  - 无指针的紧凑表示，比如 balanced parentheses。S Expression 很适合这种表示，如果消费者主要做 preorder 遍历。
  - 有些情况可能需要手写 DSA 类型。由于 rust 对自定义 metadata 的支持不够好，往往手写范围会扩散到这些 DSA 类型的引用、Box 等。
    - 当然这确实会导致代码变复杂，但我也没办法。

文档要求
- rustdoc要详细，包括 private item。启用 `missing_docs` 和 `missing_docs_in_private_items` lint，对着修即可。