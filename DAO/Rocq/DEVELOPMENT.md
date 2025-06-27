# DAO Coq Development Guide

## Selective Compilation Workflow

When working on individual files, you don't need to compile the entire project. Make automatically handles dependencies for you.

### Basic Commands

#### Compile a single file with dependencies
```bash
make src/Core/AlphaProperties.vo
```
This automatically compiles AlphaType.vo first if needed, then AlphaProperties.vo.

#### Check what would be compiled (dry run)
```bash
make -n src/Core/AlphaProperties.vo
```
Shows what make would do without actually doing it.

#### Quick syntax check
```bash
make src/Core/AlphaProperties.vos
```
Creates a `.vos` file - faster compilation for syntax checking during development.

### Force Recompilation

#### Method 1: Touch the file
```bash
touch src/Core/AlphaProperties.v
make src/Core/AlphaProperties.vo
```

#### Method 2: Remove and rebuild
```bash
rm -f src/Core/AlphaProperties.vo
make src/Core/AlphaProperties.vo
```

### Multiple Files

#### Compile several files at once
```bash
make src/Core/AlphaProperties.vo src/Logic/Basic.vo src/Logic/Ternary.vo
```

### Dependency Inspection

#### See what a file depends on
```bash
coqdep -Q src DAO src/Core/AlphaProperties.v
```

#### View the full dependency graph
```bash
cat .Makefile.coq.d
```

## Common Workflows

### Working on a theorem file
1. Edit `src/Core/AlphaProperties.v`
2. Quick check: `make src/Core/AlphaProperties.vos`
3. Full compile: `make src/Core/AlphaProperties.vo`
4. If errors, fix and repeat from step 2

### Adding a new file
1. Create `src/Logic/NewFile.v`
2. Add to `_CoqProject`
3. Regenerate makefile: `make clean && make`
4. Compile: `make src/Logic/NewFile.vo`

### Checking multiple related files
```bash
# Compile all Core files that changed
make src/Core/*.vo

# Compile all Logic files
make src/Logic/*.vo
```

## Tips

- **Tab completion works!** Type `make src/Core/Al<TAB>` to autocomplete
- **Make is incremental** - unchanged dependencies won't recompile
- **Use .vos for development** - it's much faster for iterative work
- **VSCoq integration** - After command line compilation, VSCoq will use the compiled `.vo` files

## Build Targets Reference

- `.vo` - Fully compiled and checked file
- `.vos` - Quick compilation (syntax check, light checking)
- `.vok` - Proof checking complete
- `.glob` - Global definitions (used by IDE)

## Full Project Commands

- `make all` - Compile everything
- `make clean` - Remove all build artifacts
- `make cleanall` - Deep clean (includes .aux files)
- `make check` - Compile and verify everything works