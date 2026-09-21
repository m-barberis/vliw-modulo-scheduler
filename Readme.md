# VLIW Instruction Scheduler

A C++ compiler backend that takes a basic block with a loop and produces a cycle-by-cycle
schedule for a VLIW processor, packing independent operations into the machine's parallel
issue slots.

- Builds the data dependence graph over the input program, distinguishing loop-invariant
  dependences, loop-carried dependences and intra-iteration dependences.
- Implements non-pipelined scheduling: instructions are placed as early as their operands
  and the available functional units allow, respecting each unit's latency.
- Implements software-pipelined (modulo) scheduling: computes the minimum initiation
  interval from resource and recurrence constraints, then schedules iterations to overlap
  so a new iteration starts every II cycles.
- Performs register allocation over the resulting schedule, using rotating registers so
  overlapping iterations of the pipelined loop do not overwrite each other's values.
- Validated against reference schedules across the provided test set.

```bash
./build.sh
./run.sh <input.json> <output.json>
./testall.sh
```

C++17.

---

EPFL CS-470 Advanced Computer Architecture, two-person project with Federico Vassallo. The
test set, JSON I/O format and build environment were provided by the course; the scheduler
is ours.
