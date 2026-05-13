# Data format

Each line in the data file is one record. Each record is 5-tuple

(matrix, our CS-count, Glaudell et al's CS-count, our K-count, Glaudell et al's K-count)

Each matrix is formated as a pair

(lde, matrix with Gaussian integer entries)

Each matrix with Gaussian integer entries is formated as 4 rows. Each
row is formated as 4 Gaussian integers. Each Gaussian integer is
formated as a pair

(Integer, Integer)

## Record example

((6,[[(1,-4),(-4,-2),(1,0),(-5,-1)],[(3,0),(0,-2),(3,4),(1,5)],[(2,-3),(-2,0),(-6,1),(3,1)],[(0,-5),(6,0),(0,-1),(-1,1)]]),6,6,11,11)


# Data file is [experiment_data.dat](code/experiment_data.dat).

# Code usage

## Compiling

Install Haskell and newsynth library and possible other libraries. Run
following command in the project directory to compile:

ghc +RTS -K1g -RTS -O2 Main;

## runing

./Main -data k

read matrix at line k from the data file; print the matrix, output the
synthesied circuit of our alrithm, and the lde, rcs, rkc, rlen of the
circuit. Similarly,

./Main -data k -glaudell

does the same but using Glaudell et al.'s algorithm.

./Main matrix

does the same for the given matrix (in the format defined
earlier). Similarly,

./Main matrix -glaudell

runs Glaudell et al.'s algorithm on matrix.


# Webpage app

You can run the same commands described earlier at
[here](https://www.mathstat.dal.ca/~xbian/synthCS2/index.php).
