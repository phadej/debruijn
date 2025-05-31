# 0.3.1

- Add `zipWithEnv :: (a -> b -> c) -> Env ctx a -> Env ctx b -> Env ctx c`

# 0.3

- Remove RenameA machinery
- Introduce `Contract` for environment contraction (reverse of weakening)
- `keepSub` only requires `Weaken`, not `Rename`.
