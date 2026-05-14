# Data and Code for "Exact Synthesis of Two-Qubit Clifford+CS Circuits with a Near-Minimal Number of K and CS Gates"

## Data

The data file is [experiment_data.dat](src/experiment_data.dat).

### Data Format

Each line in the data file is one record. Each record is a 5-tuple:

(matrix, our CS-count, Glaudell et al.'s CS-count, our K-count, Glaudell et al.'s K-count)

Each matrix is formatted as a pair:

(lde, matrix with Gaussian integer entries)

Each matrix with Gaussian integer entries is formatted as 4 rows. Each
row is formatted as 4 Gaussian integers. Each Gaussian integer is
formatted as a pair:

(Integer, Integer)

#### Record Example

```
((6,[[(1,-4),(-4,-2),(1,0),(-5,-1)],[(3,0),(0,-2),(3,4),(1,5)],[(2,-3),(-2,0),(-6,1),(3,1)],[(0,-5),(6,0),(0,-1),(-1,1)]]),6,6,11,11)
```

## Code

### Compiling

Install GHC and the `newsynth` library (along with any other required
dependencies). Then run the following command in the project directory:

```bash
ghc +RTS -K1g -RTS -O2 Main
```

Compilation takes about 3 minutes because Template Haskell is used to
precompute the Clifford operators at compile time.

### Running

```bash
./Main -data k
```

Reads the matrix at line `k` (0-indexed) from the data file, prints
the matrix, outputs the synthesised circuit using our algorithm, and
reports the circuit's (lde, rcs, rkc, rlen). Similarly,

```bash
./Main -data k -glaudell
```

does the same using Glaudell et al.'s algorithm.

```bash
./Main matrix
```

synthesises a circuit for the given matrix (in the format defined
above, quoted with `""`). Similarly,

```bash
./Main matrix -glaudell
```

runs Glaudell et al.'s algorithm on the given matrix.

#### Examples

```bash
./Main -data 0

./Main "((10,[[(1,19),(4,4),(12,-9),(9,18)],[(11,-21),(4,12),(9,6),(4,13)],[(-9,3),(-12,12),(-13,12),(18,3)],[(-3,1),(12,20),(-15,-12),(-10,1)]]))"
```

### Web App

The same commands can be run online at
[https://www.mathstat.dal.ca/~xbian/synthCS2/index.php](https://www.mathstat.dal.ca/~xbian/synthCS2/index.php),
without installing GHC or compiling.
