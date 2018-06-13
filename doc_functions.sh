print_filename () {
    local filename=`basename $2 .v`
    local dir=$1
    local dirwithdot=${dir//\//.}
# the coqtop of Coq-8.2pl1 used to output filenames named after their directory
#    echo "<a class=\"file\" href=\"$dirwithdot.$filename.html\">"$filename"</a>"
    echo "<a class=\"file\" href=\"$filename.html\">"$filename"</a>"
}

