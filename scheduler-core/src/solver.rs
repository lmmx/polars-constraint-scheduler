use good_lp::{
    constraint, default_solver, variable, variables, Constraint, Expression, ProblemVariables,
    Solution, SolverModel, Variable,
};
use std::collections::{HashMap, HashSet};

use crate::domain::{
    c2str, ClockVar, ConstraintRef, ConstraintType, Entity, ScheduleResult, ScheduleStrategy,
    ScheduledEvent, SchedulerConfig, WindowSpec,
};
use crate::parse;

// Custom structure to track penalty variables for better reporting
struct PenaltyVar {
    // entity_name: String,
    // instance: usize,
    var: Variable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Before,
    After,
}

/// For each subject clock s, we create binary vars x_{s,o} for every object clock o,
/// and require sum(x_{s,o}) >= 1.
/// If x_{s,o} = 1, then we enforce "s is at least 'offset' [Before|After] o".
fn apply_min_offset_at_least_one(
    builder: &mut ProblemVariables,
    add_constraint: &mut dyn FnMut(&str, Constraint),
    direction: Direction,
    subjects: &[ClockVar],
    objects: &[ClockVar],
    offset_minutes: f64,
    big_m: f64,
    label_prefix: &str,
) {
    // If no object clocks, do nothing or optionally log a warning:
    if objects.is_empty() {
        return;
    }

    for s_cv in subjects {
        // We'll gather up the x_{s,o} for each object
        let mut x_vars = Vec::with_capacity(objects.len());

        for o_cv in objects {
            // Create a binary var x_{s,o}
            let x_so = builder.add(variable().binary());
            x_vars.push(x_so);

            // The big-M constraint depends on direction
            // - AFTER => s_cv.var >= o_cv.var + offset
            // - BEFORE => s_cv.var + offset <= o_cv.var (equivalently o_cv.var - s_cv.var >= offset)
            match direction {
                Direction::After => {
                    let desc = format!(
                        "({label_prefix}) after: {} >= {} + {} if x_so=1",
                        c2str(s_cv),
                        c2str(o_cv),
                        offset_minutes
                    );
                    // s - o >= offset - M*(1 - x)
                    add_constraint(
                        &desc,
                        constraint!(s_cv.var - o_cv.var >= offset_minutes - big_m * (1.0 - x_so)),
                    );
                }
                Direction::Before => {
                    let desc = format!(
                        "({label_prefix}) before: {} + {} <= {} if x_so=1",
                        c2str(s_cv),
                        offset_minutes,
                        c2str(o_cv)
                    );
                    // o - s >= offset - M*(1 - x)
                    add_constraint(
                        &desc,
                        constraint!(o_cv.var - s_cv.var >= offset_minutes - big_m * (1.0 - x_so)),
                    );
                }
            }
        }

        // Force sum(x_{s,o}) >= 1 => the subject picks at least one object
        let mut sum_expr = Expression::from(0.0);
        for x_so in x_vars {
            sum_expr += x_so;
        }
        let desc = format!(
            "({label_prefix}) sum_x_{} >= 1 => subject {} must link to at least one object",
            s_cv.instance,
            c2str(s_cv)
        );
        add_constraint(&desc, constraint!(sum_expr >= 1.0));
    }
}

/// Main scheduling function that takes entities and config, returns optimized schedule
pub fn solve_schedule(
    entities: Vec<Entity>,
    config: SchedulerConfig,
    debug_enabled: bool,
) -> Result<ScheduleResult, String> {
    // Build category->entities map
    let mut category_map = HashMap::new();
    for e in &entities {
        category_map
            .entry(e.category.clone())
            .or_insert_with(HashSet::new)
            .insert(e.name.clone());
    }

    // Create variables for each entity instance, within [start..end]
    let mut builder = variables!();
    let mut clock_map = HashMap::new();
    for e in &entities {
        let count = e.frequency.instances_per_day();
        for i in 0..count {
            let cname = format!("{}_{}", e.name, i + 1);
            let var = builder.add(
                variable()
                    .integer()
                    .min(config.day_start_minutes as f64)
                    .max(config.day_end_minutes as f64),
            );
            clock_map.insert(
                cname,
                ClockVar {
                    entity_name: e.name.clone(),
                    instance: i + 1,
                    var,
                },
            );
        }
    }

    // We collect constraints here
    let mut constraints = Vec::new();

    // Add constraint debug helper
    let mut add_constraint = |desc: &str, c: Constraint| {
        if debug_enabled {
            eprintln!("DEBUG => {desc}");
        }
        constraints.push(c);
    };

    // Make a map: entity -> [its clockvars]
    let mut entity_clocks: HashMap<String, Vec<ClockVar>> = HashMap::new();
    for cv in clock_map.values() {
        entity_clocks
            .entry(cv.entity_name.clone())
            .or_default()
            .push(cv.clone());
    }
    for list in entity_clocks.values_mut() {
        list.sort_by_key(|c| c.instance);
    }

    // Helper to resolve references: either an entity name or a category
    let resolve_ref = |rstr: &str| -> Vec<ClockVar> {
        let mut out = Vec::new();
        for e in &entities {
            if e.name.eq_ignore_ascii_case(rstr) {
                if let Some(cl) = entity_clocks.get(&e.name) {
                    out.extend(cl.clone());
                }
            }
        }
        if !out.is_empty() {
            return out;
        }
        if let Some(nameset) = category_map.get(rstr) {
            for nm in nameset {
                if let Some(cl) = entity_clocks.get(nm) {
                    out.extend(cl.clone());
                }
            }
        }
        out
    };

    let big_m = 1440.0;

    // (1) Apply "apart/before/after" constraints
    for e in &entities {
        let eclocks = match entity_clocks.get(&e.name) {
            Some(list) => list,
            None => continue,
        };

        let ba_map: HashMap<String, (Option<f64>, Option<f64>)> = HashMap::new();
        let mut apart_intervals = Vec::new();
        let mut apart_from_list = Vec::new();

        for cexpr in &e.constraints {
            let tv_min = (cexpr.time_hours as f64) * 60.0;
            match cexpr.ctype {
                ConstraintType::Apart => {
                    apart_intervals.push(tv_min);
                }
                ConstraintType::ApartFrom => {
                    if let ConstraintRef::Unresolved(r) = &cexpr.cref {
                        apart_from_list.push((tv_min, r.clone()));
                    }
                }
                ConstraintType::Before => {
                    if let ConstraintRef::Unresolved(r) = &cexpr.cref {
                        let objects = resolve_ref(r);
                        apply_min_offset_at_least_one(
                            &mut builder,
                            &mut add_constraint,
                            Direction::Before,
                            &eclocks, // subject
                            &objects, // object
                            tv_min,
                            big_m,
                            "BeforeSome",
                        );
                    }
                }
                ConstraintType::After => {
                    if let ConstraintRef::Unresolved(r) = &cexpr.cref {
                        let objects = resolve_ref(r);
                        apply_min_offset_at_least_one(
                            &mut builder,
                            &mut add_constraint,
                            Direction::After,
                            &eclocks, // subject
                            &objects, // object
                            tv_min,
                            big_m,
                            "AfterSome",
                        );
                    }
                }
            }
        }

        // (a) "apart" for consecutive instances
        for tv in apart_intervals {
            for w in eclocks.windows(2) {
                let c1 = &w[0];
                let c2 = &w[1];
                let desc = format!("(Apart) {} - {} >= {}", c2str(c2), c2str(c1), tv);
                add_constraint(&desc, constraint!(c2.var - c1.var >= tv));
            }
        }

        // (b) "apart_from" => big-M disjunction
        for (tv, refname) in apart_from_list {
            let rvars = resolve_ref(&refname);
            for c_e in eclocks {
                for c_r in &rvars {
                    let b = builder.add(variable().binary());
                    let d1 = format!(
                        "(ApartFrom) {} - {} >= {} - bigM*(1-b)",
                        c2str(c_r),
                        c2str(c_e),
                        tv
                    );
                    add_constraint(
                        &d1,
                        constraint!(c_r.var - c_e.var >= tv - big_m * (1.0 - b)),
                    );

                    let d2 = format!(
                        "(ApartFrom) {} - {} >= {} - bigM*b",
                        c2str(c_e),
                        c2str(c_r),
                        tv
                    );
                    add_constraint(&d2, constraint!(c_e.var - c_r.var >= tv - big_m * b));
                }
            }
        }

        // (c) merges of "before & after"
        for (rname, (maybe_b, maybe_a)) in ba_map {
            let rvars = resolve_ref(&rname);
            match (maybe_b, maybe_a) {
                (Some(bv), Some(av)) => {
                    // "≥bv before" OR "≥av after" disjunction
                    for c_e in eclocks {
                        for c_r in &rvars {
                            let b = builder.add(variable().binary());
                            let d1 = format!(
                                "(Before|After) {} - {} >= {} - M*(1-b)",
                                c2str(c_r),
                                c2str(c_e),
                                bv
                            );
                            add_constraint(
                                &d1,
                                constraint!(c_r.var - c_e.var >= bv - big_m * (1.0 - b)),
                            );

                            let d2 = format!(
                                "(Before|After) {} - {} >= {} - M*b",
                                c2str(c_e),
                                c2str(c_r),
                                av
                            );
                            add_constraint(&d2, constraint!(c_e.var - c_r.var >= av - big_m * b));
                        }
                    }
                }
                (Some(bv), None) => {
                    // only "before"
                    for c_e in eclocks {
                        for c_r in &rvars {
                            let d = format!("(Before) {} - {} >= {}", c2str(c_r), c2str(c_e), bv);
                            add_constraint(&d, constraint!(c_r.var - c_e.var >= bv));
                        }
                    }
                }
                (None, Some(av)) => {
                    // only "after"
                    for c_e in eclocks {
                        for c_r in &rvars {
                            let d = format!("(After) {} - {} >= {}", c2str(c_e), c2str(c_r), av);
                            add_constraint(&d, constraint!(c_e.var - c_r.var >= av));
                        }
                    }
                }
                (None, None) => {}
            }
        }
    }

    // (2) SOFT penalty for window preferences
    // Use the penalty weight from config
    let alpha = config.penalty_weight;

    if debug_enabled {
        eprintln!(
            "--- Creating soft window penalty constraints (α = {}) ---",
            alpha
        );
    }

    // Track penalty variables for better reporting
    let mut penalty_vars: Vec<PenaltyVar> = Vec::new();

    // Track which windows are used by which instances
    let mut window_usage_vars: HashMap<String, HashMap<(usize, usize), Variable>> = HashMap::new();

    for e in &entities {
        // Skip entities with no windows - they won't have penalties
        if e.windows.is_empty() {
            continue;
        }

        if debug_enabled {
            eprintln!("Entity '{}': {} windows defined", e.name, e.windows.len());
        }

        // Get clock variables for this entity
        let eclocks = match entity_clocks.get(&e.name) {
            Some(list) => list,
            None => continue,
        };

        // If we have multiple instances and multiple windows, track window usage
        let track_window_usage = eclocks.len() > 1 && e.windows.len() > 1;
        let mut instance_window_vars = HashMap::new();

        // Process each clock variable (instance) for this entity
        for cv in eclocks {
            // Create a penalty variable p_i for this instance
            let p_i = builder.add(variable().min(0.0));

            // Store penalty info for reporting
            penalty_vars.push(PenaltyVar {
                // entity_name: e.name.clone(),
                // instance: cv.instance,
                var: p_i,
            });

            // Create one distance variable for each window
            for (w_idx, wspec) in e.windows.iter().enumerate() {
                let dist_iw = builder.add(variable().min(0.0));

                // For window distribution tracking
                if track_window_usage {
                    // Create binary variable indicating if this instance uses this window
                    let window_use_var = builder.add(variable().binary());
                    instance_window_vars.insert((cv.instance, w_idx), window_use_var);

                    // Define "using a window" as being within this many minutes of it
                    let use_threshold = config.window_tolerance;

                    // If dist_iw <= use_threshold then window_use_var = 1
                    // Using big-M: dist_iw <= use_threshold + M*(1-window_use_var)
                    let desc = format!(
                        "(WinUse) {}_{} uses win{} if dist <= {}",
                        e.name, cv.instance, w_idx, use_threshold
                    );
                    add_constraint(
                        &desc,
                        constraint!(dist_iw <= use_threshold + big_m * (1.0 - window_use_var)),
                    );

                    // If dist_iw > use_threshold then window_use_var = 0
                    // Using big-M: dist_iw >= use_threshold - M*window_use_var
                    let desc = format!(
                        "(WinUse) {}_{} doesn't use win{} if dist > {}",
                        e.name, cv.instance, w_idx, use_threshold
                    );
                    add_constraint(
                        &desc,
                        constraint!(dist_iw >= use_threshold - big_m * window_use_var),
                    );
                }

                match wspec {
                    WindowSpec::Anchor(a) => {
                        // For anchors: |t_i - a| represented with two constraints
                        // dist_iw >= t_i - a
                        let desc = format!(
                            "(Win+) dist_{}_w{} >= {} - {}",
                            cv.instance,
                            w_idx,
                            c2str(cv),
                            a
                        );
                        add_constraint(&desc, constraint!(dist_iw >= cv.var - (*a as f64)));

                        // dist_iw >= a - t_i
                        let desc = format!(
                            "(Win-) dist_{}_w{} >= {} - {}",
                            cv.instance,
                            w_idx,
                            a,
                            c2str(cv)
                        );
                        add_constraint(&desc, constraint!(dist_iw >= (*a as f64) - cv.var));
                    }
                    WindowSpec::Range(start, end) => {
                        // For ranges: 0 if inside, distance to closest edge if outside
                        // dist_iw >= start - t_i (if t_i < start)
                        let desc = format!(
                            "(WinS) dist_{}_w{} >= {} - {}",
                            cv.instance,
                            w_idx,
                            start,
                            c2str(cv)
                        );
                        add_constraint(&desc, constraint!(dist_iw >= (*start as f64) - cv.var));

                        // dist_iw >= t_i - end (if t_i > end)
                        let desc = format!(
                            "(WinE) dist_{}_w{} >= {} - {}",
                            cv.instance,
                            w_idx,
                            c2str(cv),
                            end
                        );
                        add_constraint(&desc, constraint!(dist_iw >= cv.var - (*end as f64)));
                    }
                }

                // p_i <= dist_iw => p_i will be minimum distance to any window
                let desc = format!("(Win) p_{} <= dist_{}_w{}", cv.instance, cv.instance, w_idx);
                add_constraint(&desc, constraint!(p_i <= dist_iw));

                if track_window_usage {
                    // If this window is chosen, force p_i = dist_iw
                    let window_use_var = instance_window_vars[&(cv.instance, w_idx)];
                    let desc = format!(
                        "(Win) p_{} >= dist_{}_w{} - M*(1-use)",
                        cv.instance, cv.instance, w_idx
                    );
                    add_constraint(
                        &desc,
                        constraint!(p_i >= dist_iw - big_m * (1.0 - window_use_var)),
                    );
                } else {
                    // For entities with only one window, directly force p_i = dist_iw
                    let desc =
                        format!("(Win) p_{} >= dist_{}_w{}", cv.instance, cv.instance, w_idx);
                    add_constraint(&desc, constraint!(p_i >= dist_iw));
                }
            }
        }

        // If we're tracking window usage for this entity, save the variables
        if track_window_usage {
            window_usage_vars.insert(e.name.clone(), instance_window_vars);
        }
    }

    // (3) Window distribution constraints
    // Ensure instances of the same entity use different windows when possible
    if debug_enabled {
        eprintln!("--- Adding window distribution constraints ---");
    }

    for (ename, instance_window_map) in &window_usage_vars {
        let eclocks = entity_clocks.get(ename).unwrap();
        let window_count = entities
            .iter()
            .find(|e| &e.name == ename)
            .map(|e| e.windows.len())
            .unwrap_or(0);

        if debug_enabled {
            eprintln!(
                "Entity '{}': ensuring distribution across {} windows",
                ename, window_count
            );
        }

        // Each instance must use exactly one window
        for cv in eclocks {
            let mut sum_expr = Expression::from(0.0);
            for w_idx in 0..window_count {
                if let Some(&use_var) = instance_window_map.get(&(cv.instance, w_idx)) {
                    sum_expr += use_var;
                }
            }

            let desc = format!(
                "(Dist) {}_instance{} must use exactly one window",
                ename, cv.instance
            );
            add_constraint(&desc, constraint!(sum_expr == 1.0));
        }

        // Each window can be used at most once
        // (this forces distribution across windows)
        for w_idx in 0..window_count {
            let mut sum_expr = Expression::from(0.0);
            for cv in eclocks {
                if let Some(&use_var) = instance_window_map.get(&(cv.instance, w_idx)) {
                    sum_expr += use_var;
                }
            }

            let desc = format!("(Dist) {}_window{} can be used at most once", ename, w_idx);
            add_constraint(&desc, constraint!(sum_expr <= 1.0));
        }
    }

    // Add chronological ordering constraints for instances
    for (ename, eclocks) in &entity_clocks {
        if eclocks.len() <= 1 {
            continue; // Skip entities with only one instance
        }

        for i in 0..eclocks.len() - 1 {
            let c1 = &eclocks[i]; // Earlier instance
            let c2 = &eclocks[i + 1]; // Later instance

            let desc = format!(
                "(Order) {}_instance{} must be before instance{}",
                ename, c1.instance, c2.instance
            );
            add_constraint(&desc, constraint!(c1.var <= c2.var));
        }
    }

    // (4) Build objective:
    // For earliest => minimize(sum(t_i) + alpha * sum(p_i))
    // For latest   => maximize(sum(t_i) - alpha * sum(p_i))
    //               = minimize(-sum(t_i) + alpha * sum(p_i))

    // Sum of all time variables
    let mut sum_expr = Expression::from(0.0);
    for cv in clock_map.values() {
        sum_expr += cv.var;
    }

    // Sum of all penalty variables
    let mut penalty_expr = Expression::from(0.0);
    for p in &penalty_vars {
        penalty_expr += p.var;
    }

    // Add all constraints to the problem
    if debug_enabled {
        eprintln!("Solving problem with {} constraints...", constraints.len());
    }

    let mut problem = match config.strategy {
        ScheduleStrategy::Earliest => {
            if debug_enabled {
                eprintln!("Objective: minimize(sum(t_i) + {} * sum(p_i))", alpha);
            }
            builder
                .minimise(sum_expr + alpha * penalty_expr)
                .using(default_solver)
        }
        ScheduleStrategy::Latest => {
            if debug_enabled {
                eprintln!("Objective: maximize(sum(t_i) - {} * sum(p_i))", alpha);
            }
            // Equivalent to minimize(-sum_expr + alpha * penalty_expr)
            builder
                .minimise(Expression::from(0.0) - sum_expr + alpha * penalty_expr)
                .using(default_solver)
        }
    };

    // Now actually add the constraints
    for c in constraints {
        problem = problem.with(c);
    }

    // Solve the problem
    let sol = match problem.solve() {
        Ok(s) => s,
        Err(e) => {
            return Err(format!("Solver error: {}", e));
        }
    };

    // Extract solution and organize for result
    let mut scheduled_events = Vec::new();
    for cv in clock_map.values() {
        let val = sol.value(cv.var);
        let minutes = val.round() as i32;
        scheduled_events.push(ScheduledEvent {
            entity_name: cv.entity_name.clone(),
            instance: cv.instance,
            time_minutes: minutes,
        });
    }

    // Sort events by time for better display
    scheduled_events.sort_by_key(|e| e.time_minutes);

    // Calculate total penalty
    let mut total_penalty = 0.0;
    for p in &penalty_vars {
        total_penalty += sol.value(p.var);
    }

    // Collect window usage information
    let mut window_usage = Vec::new();
    for (ename, instance_window_map) in &window_usage_vars {
        let e = entities.iter().find(|e| e.name == *ename).unwrap();

        for w_idx in 0..e.windows.len() {
            let window_desc = match &e.windows[w_idx] {
                WindowSpec::Anchor(anchor) => parse::format_minutes_to_hhmm(*anchor),
                WindowSpec::Range(start, end) => {
                    format!(
                        "{}-{}",
                        parse::format_minutes_to_hhmm(*start),
                        parse::format_minutes_to_hhmm(*end)
                    )
                }
            };

            let mut users = Vec::new();
            for (instance, idx) in instance_window_map.keys() {
                if *idx == w_idx && sol.value(instance_window_map[&(*instance, *idx)]) > 0.5 {
                    users.push(*instance);
                }
            }

            if !users.is_empty() {
                window_usage.push((ename.clone(), window_desc, users));
            }
        }
    }

    Ok(ScheduleResult {
        scheduled_events,
        total_penalty,
        window_usage,
    })
}
