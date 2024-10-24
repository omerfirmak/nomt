mod backend;
mod cli;
mod custom_workload;
mod nomt;
mod sov_db;
mod sp_trie;
mod timer;
mod transfer_workload;
mod workload;
mod reth;

use anyhow::Result;
use clap::Parser;
use cli::{Cli, Commands, InitParams, RunParams};
use timer::Timer;

pub fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Init(params) => init(params),
        Commands::Run(params) => run(params),
    }
}

pub fn init(params: InitParams) -> Result<()> {
    let workload_params = params.workload;
    let (mut init, _) = workload::parse(&workload_params, u64::max_value())?;

    let mut db = params.backend.instantiate(
        true,
        workload_params.commit_concurrency,
        workload_params.io_workers,
        workload_params.hashtable_buckets,
    );
    db.execute(None, &mut *init, None);

    Ok(())
}

pub fn run(params: RunParams) -> Result<()> {
    let workload_params = params.workload;
    let (mut init, mut workloads) = workload::parse(
        &workload_params,
        params.limits.ops.unwrap_or(u64::max_value()),
    )?;

    let mut db = params.backend.instantiate(
        params.reset,
        workload_params.commit_concurrency,
        workload_params.io_workers,
        workload_params.hashtable_buckets,
    );

    if params.reset {
        db.execute(None, &mut *init, None);
    }

    let mut timer = Timer::new(format!("{}", params.backend));
    let warmup_timeout = params
        .warm_up
        .map(|time_limit| std::time::Instant::now() + *time_limit);

    let thread_pool = rayon::ThreadPoolBuilder::new()
        .thread_name(|_| "benchtop-workload".into())
        .num_threads(workload_params.workload_concurrency as usize)
        .build()?;

    if let Some(t) = warmup_timeout {
        if workload_params.workload_concurrency == 1 {
            db.execute(Some(&mut timer), &mut *workloads[0], Some(t));
        } else {
            db.parallel_execute(Some(&mut timer), &thread_pool, &mut workloads, Some(t))?;
        };

        timer = Timer::new(format!("{}", params.backend));
    }

    let timeout = params
        .limits
        .time
        .map(|time_limit| std::time::Instant::now() + *time_limit);

    if workload_params.workload_concurrency == 1 {
        db.execute(Some(&mut timer), &mut *workloads[0], timeout);
    } else {
        db.parallel_execute(Some(&mut timer), &thread_pool, &mut workloads, timeout)?;
    };

    db.print_metrics();
    timer.print(workload_params.size);

    Ok(())
}
