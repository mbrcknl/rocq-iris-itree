#!/bin/bash
set -e
ROOTDIR=$(dirname "$(readlink -e "$0")")/..

#### CONFIGURATION #######################################################

ARTIFACT_DIR="artifact"
ARTIFACT_FILE="${ARTIFACT_DIR}.zip"

ARTIFACT_REPO_URL=git@gitlab.inf.ethz.ch:ou-plf/iris-itree.git
ARTIFACT_REPO_COMMIT=HEAD

#### UTILITIES ###########################################################

# Usage: clone_repo $url $commit $dir
function clone_repo {
    URL=$1
    COMMIT=$2
    DIR=$3

    ## Clone enough history so that we're likely to have the commit
    git clone --quiet --depth 20 ${URL} "${DIR}"
    (cd "${DIR}" && git checkout --quiet ${COMMIT})
    rm -rf "${DIR}/.git*"
}

#### INITITIALIZATION ####################################################

# Deleting previously generated artifact.
echo "Deleting previously generated artifact (no backup)."
rm -rf ${ARTIFACT_DIR} ${ARTIFACT_FILE}

#### PREPARE ARTIFACT ####################################################

# Clone the repo
clone_repo ${ARTIFACT_REPO_URL} ${ARTIFACT_REPO_COMMIT} ${ARTIFACT_DIR}
cd ${ARTIFACT_DIR}

# Extract and fetch required version of Iris (avoiding "+" which does not work on MacOS :( *)
IRIS_COMMIT=$(grep -F '"coq-iris"' < "coq-iris-itree.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
if test -z "$IRIS_COMMIT"; then echo "Could not find Iris dependency version" && exit 1; fi
echo "Iris commit: $IRIS_COMMIT"
clone_repo "https://gitlab.mpi-sws.org/iris/iris/" $IRIS_COMMIT iris/

# Extract and fetch required version of std++
STDPP_COMMIT=$(grep -F '"coq-stdpp"' < "iris/coq-iris.opam" | sed 's/.*"dev\.[0-9][0-9.-]*\.\([0-9a-z][0-9a-z]*\)".*/\1/')
if test -z "$STDPP_COMMIT"; then echo "Could not find std++ dependency version" && exit 1; fi
echo "std++ commit: $STDPP_COMMIT"
clone_repo "https://gitlab.mpi-sws.org/iris/stdpp/" $STDPP_COMMIT stdpp/

# Add appendix
cp "$ROOTDIR"/appendix/appendix.pdf .

# Write artifact version
GENDATA=.version
echo "Artifact version information"                           > ${GENDATA}
echo "================================"                      >> ${GENDATA}
echo ""                                                      >> ${GENDATA}
echo "Artifact repository commit: ${ARTIFACT_REPO_COMMIT}"        >> ${GENDATA}

cd ..

#### FINALIZING ##############################################################

# Packaging the artifact.
zip -r ${ARTIFACT_FILE} ${ARTIFACT_DIR}

# Final message.
echo -e "Artifact created as file [\e[32m${ARTIFACT_FILE}\e[0m]."
echo -e "Browse folder [\e[32m${ARTIFACT_DIR}\e[0m] to check its contents."
