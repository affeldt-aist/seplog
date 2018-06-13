source ./doc_functions.sh

begcd_cond () {
    local i=$1
    if [[ "$i" == simu.v ]] ; then
	return 1
    else
	return 0
    fi
}

print_function_begcd () {
    echo "<li>"$2
    echo "<ul>"
    echo "<li>"
    echo "<ul class=\"simu\">"
    for i in *.v; do
	if [[ "$i" == *"$3"*simu* ]]; then
	    echo "<li>"
	    print_filename $dir $i
	    echo "</li>"
	fi
    done
    echo "</ul>"
    echo "</li>"
    echo "<li>"
    echo "<ul class=\"misc\">"
    for i in *.v; do
	if [[ "$i" == *"$3"*safe_termination* ]]; then
	    echo "<li>" 
	    print_filename $dir $i 
	    echo "</li>"
	fi
    done
    echo "</ul>"
    echo "</li>"
    echo "</ul>"
    echo "</li>"
}

echo "<title>TITLE</title>"
echo "</head>"
echo "<body>"
dir="begcd"
cd $dir
    echo "<dt class=\"dt_main\"><span class=\"bfont\">"$dir/"</span>: "
cat README.doc
    echo "</dt>"
	echo "<p class=\"sublib\">Simulation between assembly programs and pseudo-code:</p>"
	for i in *.v; do
	    begcd_cond $i
	    if [ $? -eq 1 ]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Simulation for arithmetic functions: <span class=\"simu\">simulation</span> <span class=\"misc\">other properties</span></p>"
	echo "<div id=\"functions\">"
	echo "<ul class=\"crypto_list\">"

	print_function_begcd $dir 'Initialization to 0 &rarr;' 'multi_zero_'

	print_function_begcd $dir 'Initialization to 1 &rarr;' 'multi_one_'

	print_function_begcd $dir 'Comparison (<, >, =) &rarr;' 'multi_lt'

	print_function_begcd $dir 'Sign testing &rarr;' 'pick_sign'

	print_function_begcd $dir 'Array copy &rarr;' 'copy_s_'

	print_function_begcd $dir 'Signed addition &rarr;' 'multi_add_s_'

	print_function_begcd $dir 'Signed subtractions &rarr;' 'multi_sub_s'

	print_function_begcd $dir 'Doubling &rarr;' 'multi_double_u'

	print_function_begcd $dir 'Halving &rarr;' 'multi_halve_'

	print_function_begcd $dir 'Parity check &rarr;' 'multi_is_even_'

	echo "</ul>"
	echo "</div>"
	echo "<p class=\"sublib\">Application to the binary extended gcd algorithm algorithm:</p>"
	for i in *.v; do
	    if [[ "$i" == begcd*.v ]]; then
		print_filename $dir $i
	    fi
	done
