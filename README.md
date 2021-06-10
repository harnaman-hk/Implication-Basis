# Implication-Basis
## Files Info 
1. Source.cpp - Parallel code for computing an approximation of Canonical Basis
2. toCXT.cpp - Code to convert a Context in the format accepted by Source.cpp to the cxt format
3. fromCXT.cpp - Code to convert a Context in cxt format to the format accepted by Source.cpp
4. StandardDS - Contains some real-world contexts
5. StandardDSCXT - Contains some real-world contexts in cxt format
6. ArtificialDS - Contains some artificial contexts
7. ArtificialDSCXT - Contains some artificial contexts in cxt format

## Usage

### Source.cpp
- Compilation - `g++ -O3 -o algo -m64 Source.cpp -lpthread`
- Running - `./algo <Context> <Epsilon> <Delta> <strong/weak> <uniform/frequent/area/discriminativity/both> <number of threads> none`

### toCXT.cpp
- Compilation - `g++ -o toCXT toCXT.cpp`
- Running - `./toCXT <Input> > <Output>`

### fromCXT.cpp
- Compilation - `g++ -o fromCXT fromCXT.cpp`
- Running - `./fromCXT < <Input> > <Output>`
