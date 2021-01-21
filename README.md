# University-ProgrammingLanguages-FunctionalPrograming
Project to learn about symbolic processing in Haskell.

## Running with docker
To run this container in a docker container follow the steps below.
```
// pull the image if not pulled before
docker pull haskell:latest

// run a container of that image
docker run -it -v C:\Applications\GitHub\University-ProgrammingLanguages-FunctionalPrograming\Project:/home/project --name haskellContainer haskell bash
```

## Some usefull stack commands
```
stack ghci <relative path to a source file>
:quit // to return

```
