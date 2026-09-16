#include "scheduler.hpp"
#include <stdexcept>
#include <algorithm>

// version using loop (without loop.pip)
// input analysis_table is the result of the dependency analysis on the input program, containing all the useful information about dependencies and instruction types for the scheduling
// schedule is the output schedule vector we are building, where each entry is a bundle of instructions scheduled in the same cycle
// scheduled_cycle is a vector that for each instruction id gives the cycle where it is scheduled (or -1 if it is not scheduled yet)
void schedule_ASAP_basic(const std::vector<DependencyAnalysisTableEntry>& analysis_table,
                         std::vector<Bundle>& schedule,
                         const std::vector<Instruction>& instructions,
                         std::vector<int>& scheduled_cycle) {
    
    // We clear the schedule vector for rubustness (already supposed to be empty)
    schedule.clear();

    // we save the number of instructions to schedule
    const int instruction_count = static_cast<int>(instructions.size());

    // kind_by_id is a vector that for each instruction id gives the kind of the instruction, so we can easily access it during the scheduling without having to look for the instruction in the analysis table every time
    std::vector<InstructionKind> kind_by_id(static_cast<size_t>(instruction_count), InstructionKind::Unknown);

    // Defining the vectors where we'll store the different ids of the belonging instructions 
    std::vector<int> bb0_ids;
    std::vector<int> bb1_ids;
    std::vector<int> bb2_ids;
    // this is a vector of boolean of length = instr count and that initially is set to false
    std::vector<bool> is_bb1(instruction_count, false); // To quickly check if an instruction belongs to BB1

    // in this block we characterize and organize the instructions based on the basic block they belong to and we fill the kind_by_id vector
    for (int analysis_index = 0; analysis_index < static_cast<int>(analysis_table.size()); ++analysis_index) {

        // loop through all dependency analysis entries
        const DependencyAnalysisTableEntry& entry = analysis_table[analysis_index];
        if (entry.id < 0 || entry.id >= instruction_count) {
            continue;
        }
        
        // We map the kind to the entry id 
        kind_by_id[entry.id] = entry.instruction_type;

        // We divide all the entries in the basick blocks they belong to differentiate the scheduling strategy 
        switch (instructions[entry.id].basic_block) {
            case BasicBlock::BB0: bb0_ids.push_back(entry.id); break;
            case BasicBlock::BB1: bb1_ids.push_back(entry.id); is_bb1[entry.id] = true; break;
            case BasicBlock::BB2: bb2_ids.push_back(entry.id); break;
        }
    }

    // initialize the scheduled_cycle vector
    scheduled_cycle.assign(static_cast<size_t>(instruction_count), -1);

    // we schedule all the BB0 instruction first
    for (const int id : bb0_ids) {
        if (id < 0 || id >= static_cast<int>(analysis_table.size())) {
            continue;
        }

        // we place the instruction in the schedule using the schedule_entry_no_modulo function
        const DependencyAnalysisTableEntry& entry = analysis_table[id];
        schedule_entry_no_modulo(entry, instructions, schedule, scheduled_cycle, kind_by_id);
    }

    // this is an initial guess to put the loop beginning exactly after the last BB0 instr
    // if needed we will update it later
    int loop_beginning = static_cast<int>(schedule.size());

    // We have to keep possible NOP due to dependencies out of the loop (otherwise they will waste resources every loop iteration) so we schedule them here together with BB0 instructions
    for (const int id : bb1_ids) { // iterate for all the bb1
        if (id < 0 || id >= static_cast<int>(analysis_table.size())) continue;
        const DependencyAnalysisTableEntry& entry = analysis_table[id];

        // the bb0_ready is the earliest cycle when that BB1 instruction could start, considering values coming from outside the loop
        int bb0_ready = max_ready_cycle(entry.loop_invariant_dependencies, scheduled_cycle, kind_by_id); // we check the loop invariant dependencies to understand if we can already schedule the instruction at the loop beginning or if we need to push the loop beginning later
        for (const int dep_id : entry.interloop_dependencies) { // iterate for all the interloop dependencies
            if (dep_id >= 0 && dep_id < instruction_count &&
                instructions[dep_id].basic_block == BasicBlock::BB0 &&
                scheduled_cycle[dep_id] >= 0) {
                bb0_ready = std::max(bb0_ready, scheduled_cycle[dep_id] + instruction_latency(kind_by_id[dep_id]));
            }
        }
        loop_beginning = std::max(loop_beginning, bb0_ready); // we update the loop beginning if we find an instruction that cannot be scheduled at the current loop beginning (because of dependencies with BB0 instructions)
    }

    if (loop_beginning > 0) { 
        ensure_bundle_capacity(schedule, loop_beginning - 1); // if needed it makes the schedule vector longer to accomodate the loop beginning by adding empty bundles (filled with "nop")
    }

    // Separate the loop instruction from the other BB1 instructions since the loop instruction has to be scheduled at the end
    int loop_id = -1;
    std::vector<int> bb1_non_loop_ids;
    for (const int id : bb1_ids) {
        if (instructions[id].kind == InstructionKind::Loop || instructions[id].kind == InstructionKind::LoopPip) {
            loop_id = id;
        } else {
            bb1_non_loop_ids.push_back(id);
        }
    }

    if (loop_id < 0) {
    return;
    }

    // Schedule BB1 instructions (except loop) ASAP from loop_beginning.
    // Without loop.pip, the loop body has a single stage and the II equals the loop body length,
    // so we don't need modulo scheduling or the SlotTable here.
    for (const int id : bb1_non_loop_ids) {
        if (id < 0 || id >= static_cast<int>(analysis_table.size())) continue; // sanity check
        const DependencyAnalysisTableEntry& entry = analysis_table[id];

        // We calculate the earliest cycle we can schedule the instruction based on its dependencies (local, loop invariant, and interloop dependencies)
        int earliest = max_ready_cycle(entry.local_dependencies, scheduled_cycle, kind_by_id);
        earliest = std::max(earliest, max_ready_cycle(entry.loop_invariant_dependencies, scheduled_cycle, kind_by_id));
        earliest = std::max(earliest, loop_beginning);

        int cycle = earliest;
        // iteratively look for the first cycle where we can place the instruction (checking bundle capacity) and place the instruction there
        while (true) {
            ensure_bundle_capacity(schedule, cycle);
            if (can_place_in_bundle(schedule[cycle], entry.instruction_type)) break;
            ++cycle;
        }
        place_in_bundle(schedule[cycle], entry.instruction_type, instructions[id].raw_text);
        scheduled_cycle[id] = cycle;
    }

    // here it searches for the last cycle where we scheduled a BB1 instruction
    int last_bb1_cycle = loop_beginning; // We start from here 
    for (const int id : bb1_non_loop_ids) {
        last_bb1_cycle = std::max(last_bb1_cycle, scheduled_cycle[id]);
    }

    // We try to schedule the loop instruction at the end of the loop ASAP 
    int loop_cycle = last_bb1_cycle;
    while (true) {
        ensure_bundle_capacity(schedule, loop_cycle);
        if (can_place_in_bundle(schedule[loop_cycle], InstructionKind::Loop)) break;
        ++loop_cycle;
    }
    place_in_bundle(schedule[loop_cycle], InstructionKind::Loop, instructions[loop_id].raw_text);
    scheduled_cycle[loop_id] = loop_cycle;

    // We compute the length of the loop body (ii in this case)
    int ii = loop_cycle - loop_beginning + 1; // loop_cycle is the cycle where we placed the loop instr

    // Check interloop constraints (equation 2). If violated, push the loop instruction down.
    while (!interloop_constraints_satisfied(bb1_ids, is_bb1, analysis_table,
                                            scheduled_cycle, kind_by_id, ii)) {
        schedule[loop_cycle].BRANCH = "nop";
        ++loop_cycle;
        ensure_bundle_capacity(schedule, loop_cycle);
        while (!can_place_in_bundle(schedule[loop_cycle], InstructionKind::Loop)) {
            ++loop_cycle;
            ensure_bundle_capacity(schedule, loop_cycle);
        }
        place_in_bundle(schedule[loop_cycle], InstructionKind::Loop, instructions[loop_id].raw_text);
        scheduled_cycle[loop_id] = loop_cycle;
        ii = loop_cycle - loop_beginning + 1;

        if (ii > 100) {
            throw std::runtime_error("Scheduling failed: exceeded reasonable II limit.");
        }
    }

    // BB2 is NOT scheduled here — alloc_b may push the loop instruction down
    // so we don't know the final loop position yet.
    // schedule_bb2() will handle it after alloc_b finishes.
}

// schedules BB2 instructions after the final loop position is known
// called after alloc_b since alloc_b can push the loop instruction down
void schedule_bb2(const std::vector<DependencyAnalysisTableEntry>& analysis_table,
                  std::vector<Bundle>& schedule,
                  const std::vector<Instruction>& instructions,
                  std::vector<int>& scheduled_cycle) {

    const int instruction_count = static_cast<int>(instructions.size());

    // we need kind_by_id just like in the other schedulers
    std::vector<InstructionKind> kind_by_id(instruction_count, InstructionKind::Unknown);
    for (int i = 0; i < static_cast<int>(analysis_table.size()); ++i) {
        if (analysis_table[i].id >= 0 && analysis_table[i].id < instruction_count) {
            kind_by_id[analysis_table[i].id] = analysis_table[i].instruction_type;
        }
    }

    // find the loop instruction's final cycle so we know where BB2 starts
    int loop_cycle = -1;
    bool is_loop_pip = false;
    for (int i = 0; i < instruction_count; ++i) {
        if (instructions[i].kind == InstructionKind::Loop || instructions[i].kind == InstructionKind::LoopPip) {
            loop_cycle = scheduled_cycle[i];
        }
    }
    // detect loop.pip from the schedule itself (alloc_r rewrites "loop" to "loop.pip")
    for (int c = 0; c < static_cast<int>(schedule.size()); ++c) {
        if (schedule[c].BRANCH.rfind("loop.pip", 0) == 0) {
            is_loop_pip = true;
            break;
        }
    }

    // BB2 must start after the loop instruction
    int bb2_start = (loop_cycle >= 0) ? loop_cycle + 1 : static_cast<int>(schedule.size());

    // schedule each BB2 instruction using the same schedule_entry_no_modulo we use for BB0
    // but with a minimum cycle of bb2_start and post-loop + loop-invariant dependencies
    for (int i = 0; i < instruction_count; ++i) {
        if (instructions[i].basic_block != BasicBlock::BB2) continue;
        if (i < 0 || i >= static_cast<int>(analysis_table.size())) continue;

        const DependencyAnalysisTableEntry& entry = analysis_table[i];

        // compute the earliest cycle from local dependencies
        int earliest = max_ready_cycle(entry.local_dependencies, scheduled_cycle, kind_by_id);

        // For loop.pip: by the time BB2 runs the epilogue has fully drained,
        // so all post-loop values are already available. We only need bb2_start.
        // For basic loop: post-loop deps need latency checks since the value
        // is produced within the loop body on the last iteration.
        if (!is_loop_pip) {
            std::vector<int> deps = entry.post_loop_dependencies;
            deps.insert(deps.end(), entry.loop_invariant_dependencies.begin(), entry.loop_invariant_dependencies.end());
            earliest = std::max(earliest, max_ready_cycle(deps, scheduled_cycle, kind_by_id));
        } else {
            // still check loop-invariant deps (BB0 producers) since they have real cycle positions
            earliest = std::max(earliest, max_ready_cycle(entry.loop_invariant_dependencies, scheduled_cycle, kind_by_id));
        }

        // but never before bb2_start
        earliest = std::max(earliest, bb2_start);

        // find a cycle with a free slot
        int cycle = earliest;
        while (true) {
            ensure_bundle_capacity(schedule, cycle);
            if (can_place_in_bundle(schedule[cycle], entry.instruction_type)) break;
            ++cycle;
        }
        place_in_bundle(schedule[cycle], entry.instruction_type, instructions[i].raw_text);
        scheduled_cycle[i] = cycle;
    }
}

// version using loop.pip
void schedule_ASAP_advanced(const std::vector<DependencyAnalysisTableEntry>& analysis_table,
                            std::vector<Bundle>& schedule,
                            const std::vector<Instruction>& instructions,
                            std::vector<int>& scheduled_cycle,
                            int& out_ii,
                            int& out_loop_beginning,
                            int& out_num_stages,
                            std::vector<int>& out_stage_by_id) {

    schedule.clear();
    const int instruction_count = static_cast<int>(instructions.size());

    std::vector<InstructionKind> kind_by_id(static_cast<size_t>(instruction_count), InstructionKind::Unknown);

    std::vector<int> bb0_ids;
    std::vector<int> bb1_ids;
    std::vector<int> bb2_ids;
    std::vector<bool> is_bb1(instruction_count, false);

    // the for iterates over the length of the analysis table
    for (int analysis_index = 0; analysis_index < static_cast<int>(analysis_table.size()); ++analysis_index) {
        
        const DependencyAnalysisTableEntry& entry = analysis_table[analysis_index];
        if (entry.id < 0 || entry.id >= instruction_count) continue; // Sanity check

        kind_by_id[entry.id] = entry.instruction_type;

        // depending on the bb type it belongs we put in the corrisponding vector
        switch (instructions[entry.id].basic_block) {
            case BasicBlock::BB0: bb0_ids.push_back(entry.id); break;
            case BasicBlock::BB1: bb1_ids.push_back(entry.id); is_bb1[entry.id] = true; break;
            case BasicBlock::BB2: bb2_ids.push_back(entry.id); break;
        }
    }

    // reset scheduled_cycle
    scheduled_cycle.assign(static_cast<size_t>(instruction_count), -1);

    // BB0 scheduling
    for (const int id : bb0_ids) {

        if (id < 0 || id >= static_cast<int>(analysis_table.size())) continue;
        const DependencyAnalysisTableEntry& entry = analysis_table[id];
        schedule_entry_no_modulo(entry, instructions, schedule, scheduled_cycle, kind_by_id);
    }

    // Push loop_beginning past any BB0 latency tails to avoid bubbles 
    int loop_beginning = static_cast<int>(schedule.size());

    for (const int id : bb1_ids) {
        if (id < 0 || id >= static_cast<int>(analysis_table.size())) continue;
        const DependencyAnalysisTableEntry& entry = analysis_table[id];

        int bb0_ready = max_ready_cycle(entry.loop_invariant_dependencies, scheduled_cycle, kind_by_id);
        for (const int dep_id : entry.interloop_dependencies) {
            if (dep_id >= 0 && dep_id < instruction_count &&
                instructions[dep_id].basic_block == BasicBlock::BB0 &&
                scheduled_cycle[dep_id] >= 0) {
                bb0_ready = std::max(bb0_ready, scheduled_cycle[dep_id] + instruction_latency(kind_by_id[dep_id]));
            }
        }
        loop_beginning = std::max(loop_beginning, bb0_ready);
    }
    if (loop_beginning > 0) {
        ensure_bundle_capacity(schedule, loop_beginning - 1);
    }

    // Separate loop.pip from other BB1 instructions
    int loop_id = -1;
    std::vector<int> bb1_non_loop_ids;
    for (const int id : bb1_ids) {
        if (instructions[id].kind == InstructionKind::Loop || instructions[id].kind == InstructionKind::LoopPip) {
            loop_id = id;
        } else {
            bb1_non_loop_ids.push_back(id);
        }
    }

    if (loop_id < 0) {
    return;
    }

    // BB1 modulo scheduling with increasing II
    int ii = std::max(1, calculate_II_res(instructions));

    while (true) { // we will keep trying to schedule BB1 instructions with increasing II until we find a valid schedule that satisfies all constraints and so break
        SlotTable slot_table;
        slot_table.init_reset(ii); // we reset and initialize the slot table for the new II

        for (const int id : bb1_ids) {
            scheduled_cycle[id] = -1; // we reset the scheduled cycle for all the BB1 instructions since we will try to reschedule them with the new II
        }
        schedule.resize(loop_beginning); // we reset the schedule to the loop beginning, since all the BB1 instructions will be rescheduled starting from the loop beginning (we keep the BB0 instructions that are before the loop beginning)

        bool failed = false; // this flag will be set to true if we find an instruction that cannot be scheduled with the current II, so we have to try again with a higher II

        for (const int id : bb1_non_loop_ids) {
            if (id < 0 || id >= static_cast<int>(analysis_table.size())) continue;
            const DependencyAnalysisTableEntry& entry = analysis_table[id];

            int earliest = max_ready_cycle(entry.local_dependencies, scheduled_cycle, kind_by_id);
            earliest = std::max(earliest, max_ready_cycle(entry.loop_invariant_dependencies, scheduled_cycle, kind_by_id));
            earliest = std::max(earliest, loop_beginning);

            for (const int dep_id : entry.interloop_dependencies) { // we iterate for all the interloop dependencies to check if they are scheduled in BB1 and if they are scheduled we apply the equation 2 to update the earliest cycle where we can schedule the instruction
                // saity check
                if (dep_id < 0 || dep_id >= instruction_count) continue;

                // we skip the bb0 producers 
                if (!is_bb1[dep_id]) continue;

                // we skip if the producer is not skeduled yet (it means that the producer is after the consumer in program order, so we will check the constraint later when we will have scheduled the producer)
                if (scheduled_cycle[dep_id] < 0) continue;

                // we apply the equation 2 to update the earliest cycle where we can schedule the 
                // instruction based on the producer cycle, the producer latency and the current II 
                int prod_cycle = scheduled_cycle[dep_id];
                int prod_latency = instruction_latency(kind_by_id[dep_id]);
                
                int min_cycle_required = prod_cycle + prod_latency - ii;
                
                // we update the earliest
                earliest = std::max(earliest, min_cycle_required);
            }

            int cycle = earliest;
            while (true) { 
                if (cycle > loop_beginning + ii * 20) { // sanity check to avoid infinite loops in case of bugs 
                    //(we allow to go up to 20 II windows after the loop beginning, which should be more than enough 
                    //for any reasonable schedule)
                    failed = true;  
                    break;
                }
                ensure_bundle_capacity(schedule, cycle);
                bool hardware_is_free = slot_table.can_schedule(cycle, entry.instruction_type);
                bool text_bundle_is_free = can_place_in_bundle(schedule[cycle], entry.instruction_type);
                if (hardware_is_free && text_bundle_is_free) {
                    break;
                }
                ++cycle;
            }
            if (failed) {
                break;
            }

            place_in_bundle(schedule[cycle], entry.instruction_type, instructions[id].raw_text);
            slot_table.reserve_resources(cycle, entry.instruction_type);
            scheduled_cycle[id] = cycle;
        }

        if (failed) {
            ii++;
            if (ii > 100) throw std::runtime_error("Scheduling failed: exceeded reasonable II limit.");
            continue;
        }

        // Validate all interloop constraints that couldn't be checked during scheduling
        // (producers that appear after their consumer in program order)
        if (!interloop_constraints_satisfied(bb1_ids, is_bb1, analysis_table,
                                             scheduled_cycle, kind_by_id, ii)) {
            ii++;
            if (ii > 100) throw std::runtime_error("Scheduling failed: exceeded reasonable II limit.");
            continue;
        }

        break;
    }

    // At this point, we have successfully scheduled all BB1 instructions (except the loop instruction) with a valid II. 
    // Now we just need to place the loop instruction 
    // it must be the last bundle of the first II window.
    int loop_cycle = loop_beginning + ii - 1;

    ensure_bundle_capacity(schedule, loop_cycle); // Ensure the row exists 

    // place the instruction in the BRANCH slot of that specific bundle.
    place_in_bundle(schedule[loop_cycle], InstructionKind::LoopPip, instructions[loop_id].raw_text);

    // record its position 
    scheduled_cycle[loop_id] = loop_cycle;

    // We need to know how many stages each instruction goes forward.
    // This is essential for predication and register allocation
    std::vector<int> stage_by_id(instruction_count, -1);
    int max_stage = 0;

    for (const int id : bb1_ids) {
        int cycle = scheduled_cycle[id];
        
        // We only care about instructions that are actually part of the loop body
        if (cycle >= loop_beginning) {
            
            // The stage index is how many II-windows the instruction has shifted 
            // away from the start of its own iteration.
            int relative_cycle = cycle - loop_beginning;
            int stage = relative_cycle / ii; 
            
            stage_by_id[id] = stage;
            
            if (stage > max_stage) {
                max_stage = stage;
            }
        }
    }

    // The total number of stages is the index of the last stage + 1
    int num_stages = max_stage + 1;

    // pass computed values back to the caller for register allocation
    out_ii = ii;
    out_loop_beginning = loop_beginning;
    out_num_stages = num_stages;
    out_stage_by_id = stage_by_id;
}

int calculate_II_res(const std::vector<Instruction>& instructions) {

    int alu_count = 0;
    int mul_count = 0;
    int mem_count = 0;

    // we count the number of ALU, MUL, and MEM instructions in BB1 to determine the II_res
    // they will be useful for the formula calculattion for II_res 
    for (const auto& instr : instructions) {
        
        if (instr.basic_block != BasicBlock::BB1) {
            continue; // Only consider instructions in BB1
        }

        switch (instr.kind) {
            case InstructionKind::Add:
            case InstructionKind::Addi:
            case InstructionKind::Sub:
            case InstructionKind::Mov:
                alu_count++;
                break;
            case InstructionKind::Mulu:
                mul_count++;
                break;
            case InstructionKind::Ld:
            case InstructionKind::St:
                mem_count++;
                break;
            default:
                break; // Ignore other instruction types
        }
    }

    // we use the alu_count + 1 for doing the ceiling of the division by 2
    int ii_alu = (alu_count + 1) / 2; // Each bundle can have up to 2 ALU instructions
    int ii_mul = mul_count; // Each bundle can have 1 MUL instruction
    int ii_mem = mem_count; // Each bundle can have 1 MEM instruction

    // The II_res is the maximum of the three calculated values
    int ii_res = std::max({ii_alu, ii_mul, ii_mem, 1}); // (the 1 is the ensure is at least 1)

    return ii_res;
}
