#!/bin/bash
set -e
ROOTDIR=$(dirname "$(readlink -e "$0")")/..

#### CONFIGURATION #######################################################

ARTIFACT_DIR="artifact"
ARTIFACT_FILE="${ARTIFACT_DIR}.tar.gz"

ARTIFACT_REPO_URL=git@gitlab.inf.ethz.ch:ou-plf/iris-itree.git
ARTIFACT_REPO_COMMIT=HEAD

#### UTILITIES ###########################################################

# Usage: clone_repo $url $commit $dir
function clone_repo {
    URL=$1
    COMMIT=$2
    DIR=$3

    ## Clone enough history so that we're likely to have the commit
    git clone --quiet ${URL} "${DIR}"
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

# Remove artifact script
rm artifact.sh
rm -rf .git/
rm .gitignore
rm .gitlab-ci.yml

# Write artifact version
GENDATA=.version
echo "Artifact version information"                           > ${GENDATA}
echo "================================"                      >> ${GENDATA}
echo ""                                                      >> ${GENDATA}
echo "Artifact repository commit: ${ARTIFACT_REPO_COMMIT}"        >> ${GENDATA}

cd ..

#### FINALIZING ##############################################################

# Packaging the artifact.
tar -czvf ${ARTIFACT_FILE} ${ARTIFACT_DIR} --owner=anon --group=anon

# Final message.
echo -e "Artifact created as file [\e[32m${ARTIFACT_FILE}\e[0m]."
echo -e "Browse folder [\e[32m${ARTIFACT_DIR}\e[0m] to check its contents."
