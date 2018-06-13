source ./doc_functions.sh

echo "<title>TITLE</title>"
echo "</head>"
echo "<body>"
dir="seplog"
cd $dir
    echo "<dt class=\"dt_main\"><span class=\"bfont\">"$dir/"</span>: "
cat README.doc
    echo "</dt>"
	echo "<p class=\"sublib\">Standard separation logic:</p>"
	for i in *.v; do
	    if [[ "$i" != *topsy* ]] && [[ "$i" != *frag* ]] && [[ "$i" != *expr_b_dp* ]] && [[ "$i" != *LSF* ]]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">A certified verifier for a fragment of separation logic:</p>"
	for i in *.v; do
	    if [[ "$i" == *frag* ]] || [[ "$i" == *expr_b_dp* ]] || [[ "$i" == *LSF* ]]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Formal verification of the heap manager of an operating system:</p>"
	for i in *.v; do
	    if [[ "$i" == *topsy* ]] ; then
		print_filename $dir $i
	    fi
	done

