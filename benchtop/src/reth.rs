use crate::{backend::Transaction, timer::Timer, workload::Workload};

use reth_db::{cursor::{DbCursorRO, DbCursorRW, DbDupCursorRO, DbDupCursorRW}, init_db, mdbx::DatabaseArguments, tables, transaction::{DbTx, DbTxMut}, Database, DatabaseEnv};
use reth_primitives_traits::{Account, StorageEntry};
use reth_trie::{hashed_cursor::HashedCursor, proof::Proof, updates::TrieUpdates, HashedPostState, HashedPostStateSorted, StateRoot, StoredNibbles};
use reth_trie_db::{DatabaseHashedAccountCursor, DatabaseProof, DatabaseStateRoot};
use alloy_primitives::{keccak256, FixedBytes, U256};
use itertools::Itertools;


const RETH_DB_FOLDER: &str = "reth_db";

use std::{collections::HashSet, marker::PhantomData};

pub struct UpdateWriter<Tx: DbTxMut + DbTx> {
    _marker: PhantomData<Tx>,
}

impl<Tx: DbTxMut + DbTx> UpdateWriter<Tx> {
    // Copied from Reth
    fn write_trie_updates(tx: &Tx,  trie_updates: &TrieUpdates) -> usize {
        if trie_updates.is_empty() {
            return 0
        }

        // Track the number of inserted entries.
        let mut num_entries = 0;

        // Merge updated and removed nodes. Updated nodes must take precedence.
        let mut account_updates = trie_updates
            .removed_nodes_ref()
            .iter()
            .filter_map(|n| {
                (!trie_updates.account_nodes_ref().contains_key(n)).then_some((n, None))
            })
            .collect::<Vec<_>>();
        account_updates.extend(
            trie_updates.account_nodes_ref().iter().map(|(nibbles, node)| (nibbles, Some(node))),
        );
        // Sort trie node updates.
        account_updates.sort_unstable_by(|a, b| a.0.cmp(b.0));

        let mut account_trie_cursor = tx.cursor_write::<tables::AccountsTrie>().unwrap();
        for (key, updated_node) in account_updates {
            let nibbles = StoredNibbles(key.clone());
            match updated_node {
                Some(node) => {
                    if !nibbles.0.is_empty() {
                        num_entries += 1;
                        account_trie_cursor.upsert(nibbles, node.clone()).unwrap();
                    }
                }
                None => {
                    num_entries += 1;
                    if account_trie_cursor.seek_exact(nibbles).unwrap().is_some() {
                        account_trie_cursor.delete_current().unwrap();
                    }
                }
            }
        }
        num_entries
    }

    fn write_hashed_state(tx: &Tx, hashed_state: &HashedPostStateSorted) {
        // Write hashed account updates.
        let mut hashed_accounts_cursor = tx.cursor_write::<tables::HashedAccounts>().unwrap();
        for (hashed_address, account) in hashed_state.accounts().accounts_sorted() {
            if let Some(account) = account {
                hashed_accounts_cursor.upsert(hashed_address, account).unwrap();
            } else if hashed_accounts_cursor.seek_exact(hashed_address).unwrap().is_some() {
                hashed_accounts_cursor.delete_current().unwrap();
            }
        }

        // Write hashed storage changes.
        let sorted_storages = hashed_state.account_storages().iter().sorted_by_key(|(key, _)| *key);
        let mut hashed_storage_cursor =
            tx.cursor_dup_write::<tables::HashedStorages>().unwrap();
        for (hashed_address, storage) in sorted_storages {
            if storage.is_wiped() && hashed_storage_cursor.seek_exact(*hashed_address).unwrap().is_some() {
                hashed_storage_cursor.delete_current_duplicates().unwrap();
            }

            for (hashed_slot, value) in storage.storage_slots_sorted() {
                let entry = StorageEntry { key: hashed_slot, value };
                if let Some(db_entry) =
                    hashed_storage_cursor.seek_by_key_subkey(*hashed_address, entry.key).unwrap()
                {
                    if db_entry.key == entry.key {
                        hashed_storage_cursor.delete_current().unwrap();
                    }
                }

                if !entry.value.is_zero() {
                    hashed_storage_cursor.upsert(*hashed_address, entry).unwrap();
                }
            }
        }
    }
}


pub struct RethDB {
    pub database_env: DatabaseEnv,
}

impl RethDB {
    pub fn open(reset: bool) -> Self {
        if reset {
            // Delete previously existing db
            let _ = std::fs::remove_dir_all(RETH_DB_FOLDER);
        }

        Self {
            database_env: init_db(RETH_DB_FOLDER, DatabaseArguments::default()).unwrap()  
        }
    }

    pub fn execute(&mut self, mut timer: Option<&mut Timer>, workload: &mut dyn Workload) {
        let _timer_guard_total = timer.as_mut().map(|t| t.record_span("workload"));
        let db_tx = self.database_env.tx().unwrap();

        let db_cursor = db_tx.new_cursor::<tables::HashedAccounts>().unwrap();
        let account_cursor = DatabaseHashedAccountCursor::new(db_cursor);
        let mut transaction = RethTx {
            timer: timer,
            memory: HashedPostState::default(),
            persistent: Box::new(account_cursor),
            reads: HashSet::new(),
        };
        workload.run_step(&mut transaction);


        let _timer_guard_commit = transaction.timer.as_mut().map(|t| t.record_span("commit_and_prove"));

        let res = StateRoot::overlay_root_with_updates(&db_tx, transaction.memory.clone()).unwrap();
        let rw_tx = self.database_env.tx_mut().unwrap();
        UpdateWriter::write_trie_updates(&rw_tx, &res.1);
        UpdateWriter::write_hashed_state(&rw_tx, &transaction.memory.into_sorted());
        rw_tx.inner.commit().unwrap();

        let db_tx = self.database_env.tx().unwrap();
        let proof = Proof::from_tx(&db_tx);

        let targets = transaction.reads.iter().map(|k| (*k, HashSet::new())).collect();
        let _ = proof.multiproof(targets);
    }
}

pub struct RethTx<'a> {
    timer: Option<&'a mut Timer>,
    memory: HashedPostState,
    persistent: Box<dyn HashedCursor<Value = Account>>,
    reads: HashSet<FixedBytes<32>>
}

impl<'a> Transaction for RethTx<'a> {
    fn read(&mut self, key: &[u8]) -> Option<Vec<u8>> {
        let _timer_guard_read = self.timer.as_mut().map(|t| t.record_span("read"));
        let hashed_key = keccak256(key);
        let acc = self.memory.accounts.get(&hashed_key);
        if let Some(Some(acc)) = acc {
            let balance_vec = acc.balance.to_be_bytes_vec();
            return Some(balance_vec[balance_vec.len()-8..].to_vec());
        }

        match self.persistent.seek(hashed_key) {
            Ok(Some((key, account))) => {
                if key.eq(&hashed_key) {
                    let balance_vec = account.balance.to_be_bytes_vec();        
                    Some(balance_vec[balance_vec.len()-8..].to_vec())
                } else {
                    None
                }
            }
            _ => None
        }
    }

    fn note_read(&mut self, key: &[u8], _: Option<Vec<u8>>) {
        self.reads.insert(keccak256(key));
    }

    fn write(&mut self, key: &[u8], value: Option<&[u8]>) {
        let hashed_key = keccak256(key);
        

        let acc = if let Some(value) = value {
            Some(Account {
                nonce: 1,
                bytecode_hash: None,
                balance: U256::from_be_slice(value),
            })
        } else {
            None
        };
        self.memory.accounts.insert(hashed_key, acc);
    }
}