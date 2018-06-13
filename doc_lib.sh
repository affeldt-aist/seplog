source ./doc_functions.sh

echo "<title>TITLE</title>"
echo "</head>"
echo "<body>"
dir="lib"
cd $dir

    echo "<dt class=\"dt_main\"><span class=\"bfont\">"$dir/"</span>: "
cat README.doc
    echo "</dt>"
	for i in *.v; do
	    print_filename $dir $i
	done


