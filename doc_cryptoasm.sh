source ./doc_functions.sh

cryptoasm_cond () {
    local i=$1
    if [[ "$i" == *_prg.v ]] || [[ "$i" == *_termination.v ]] || 
	[[ "$i" == *_triple.v ]] || [[ "$i" == *bbs* ]] || 
	[[ "$i" == *goto* ]] || [[ "$i" == *compile* ]]; then
	return 0
    else
	return 1
    fi
}

print_function () {
    echo "<li>"$2
    echo "<ul>"
    echo "<li>"
    echo "<ul class=\"prg\">"
    for i in *.v; do
	if [[ "$i" == *"$3"*prg* ]]; then
	    echo "<li>"
	    print_filename $dir $i
	    echo "</li>"
	fi
    done
    echo "</ul>"
    echo "</li>"
    echo "<li>"
    echo "<ul class=\"triple\">"
    for i in *.v; do
	if [[ "$i" == *"$3"*triple* ]]; then
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
	if [[ "$i" == *"$3"* ]] && [[ "$i" != *"$3"*prg* ]] && [[ "$i" != *"$3"*triple* ]]; then
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
dir="cryptoasm"
cd $dir
    echo "<dt class=\"dt_main\"><span class=\"bfont\">"$dir/"</span>: "
cat README.doc
    echo "</dt>"
	echo "<p class=\"sublib\">Separation logic for SmartMIPS:</p>"
	for i in *.v; do
	    cryptoasm_cond $i
	    if [ $? -eq 1 ]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Illustrative example of SGoto:</p>"
	for i in *.v; do
	    if [[ "$i" == *goto* ]] || [[ "$i" == *compile* ]] ; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Formal verifications of cryptographic functions: <span class=\"prg\">program</span> <span class=\"triple\">functional correctness</span> <span class=\"misc\">other properties</span></p>"
	echo "<div id=\"functions\">"
	echo "<ul class=\"crypto_list\">"

	echo "<div id=\"kamoku\">Multi-precision unsigned arithmetic</div>"

	print_function $dir 'Initialization to 0 &rarr;' 'multi_zero_u'

	print_function $dir 'Initialization to 1 &rarr;' 'multi_one_u'

	print_function $dir 'Parity check &rarr;' 'multi_is_even_u'
	
	print_function $dir 'Zero testing &rarr;' 'multi_is_zero_u'

	print_function $dir 'Array copy &rarr;' 'copy_u_u'

	print_function $dir 'Additions &rarr;' 'multi_add_u_u'

	print_function $dir 'Subtractions &rarr;' 'multi_sub_u_u'

	print_function $dir 'Multiplication &rarr;' 'multi_mul_u_u'

	print_function $dir 'Halving &rarr;' 'multi_halve_u'

	print_function $dir 'Doubling &rarr;' 'multi_double_u'

	print_function $dir 'Comparison (<, >, =) &rarr;' 'multi_lt'

	print_function $dir 'Montgomery multiplication &rarr;' 'mont_mul'

	print_function $dir 'Montgomery squaring &rarr;' 'mont_square'

	print_function $dir 'Montgomery exponentiation &rarr;' 'mont_exp'

	print_function $dir 'BBS pseudorandom bit generator &rarr;' 'bbs'

	echo "<div id=\"kamoku\">Multi-precision signed arithmetic</div>"

	print_function $dir 'Initialization to 0 &rarr;' 'multi_zero_s'

	print_function $dir 'Initialization to 1 &rarr;' 'multi_one_s'

	print_function $dir 'Negation &rarr;' 'multi_negate'

	print_function $dir 'Sign testing &rarr;' 'pick_sign'

	print_function $dir 'Array copy &rarr;' 'copy_s_'

	print_function $dir 'Signed addition &rarr;' 'multi_add_s_'

	print_function $dir 'Signed subtractions &rarr;' 'multi_sub_s'
	
	print_function $dir 'Signed halving &rarr;' 'multi_halve_s'

	echo "</ul>"
	echo "</div>"
