## 运行

```bash
cargo run --bin harness
```

会得到：

```text
stats.csv
stats.jsonl
```

## 关键点

热路径只有：

```rust
// Normal memory access.
inc_steps();
inc_conflicts();
inc_propagations(...);

// load with relaxed ordering.
if TICK.load(Ordering::Relaxed) {
    TICK.store(false, Ordering::Relaxed);
    let sample = take_stats(...);
    emit_stats_line(&sample);
}
```