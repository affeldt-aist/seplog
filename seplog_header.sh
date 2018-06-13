for file in `cat seplog_files.txt`
do
    sed -i -e '1i (* seplog (c) AIST 2005-2015. R. Affeldt, N. Marti, et al. GNU GPLv3. *)' $file
done
