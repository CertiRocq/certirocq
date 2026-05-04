#!/usr/bin/env bash

PLUGIN=$1
if [ ! -d "${PLUGIN}" ]
then
    PLUGIN="plugins/${PLUGIN}"
fi

PLUGIN_NAME=$(basename "${PLUGIN}")
EPATH=

echo "Plugin: " ${PLUGIN}

if [ "${PLUGIN_NAME}" == "plugin" ]
then 
    echo "Building optimized ML plugin"
    EPATH="theories/Extraction"
else
    if [ "${PLUGIN_NAME}" == "cplugin" ]
    then
        echo "Building vanila ML plugin"
        EPATH="theories/ExtractionVanilla"
    else
        echo "Don't know which plugin to build"
        exit 1
    fi 
fi

echo "Copying result of extraction"

rm -rf ${PLUGIN}/extraction || true

if [ ! -d "${PLUGIN}/extraction" ]
then
    mkdir ${PLUGIN}/extraction
fi

# Copy the extracted code to the extraction destination
cd ${EPATH}

# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=../../"${PLUGIN}"/extraction/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  # echo "Copying " $i "to" $newi;
  cp $i $newi;
done

cd ../..

# Speciale case for files that are only uppercase!
cd ${PLUGIN}/extraction
mv aST.ml AST.ml
mv aST.mli AST.mli
# We compile with -rectypes, so these definitions are badly interepreted
sed -e "s/type int = int/type nonrec int = int/" integers.mli > integers.mli.tmp && mv -f integers.mli.tmp integers.mli
sed -e "s/type int = int/type nonrec int = int/" integers.ml > integers.ml.tmp && mv -f integers.ml.tmp integers.ml
cd ..
patch -p0 < patch_ints # Fix 'int' definitions in 8.14 clashing with pervarsives' int
cd ..
