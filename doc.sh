print_filename () {
    local filename=`basename $2 .v`
    local dir=$1
    local dirwithdot=${dir//\//.}
# the coqtop of Coq-8.2pl1 used to output filenames named after their directory
#    echo "<a class=\"file\" href=\"$dirwithdot.$filename.html\">"$filename"</a>"
    echo "<a class=\"file\" href=\"$filename.html\">"$filename"</a>"
}

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

begcd_cond () {
    local i=$1
    if [[ "$i" == simu.v ]] ; then
	return 1
    else
	return 0
    fi
}

C_cond () {
    local i=$1
    if [[ "$i" == POLAR*.v ]] || [[ "$i" == rfc5246.v ]]; then
	return 0
    else
	return 1
    fi
}

POLAR_cond () {
    local i=$1
    if [[ "$i" == POLAR*.v ]]; then
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

print_function_begcd_special () {
    echo "<li>"$2
    echo "<ul>"
    echo "<li>"
    echo "<ul class=\"simu\">"
    for i in *.v; do
	if [[ "$i" == "$3" ]]; then
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

echo "<p class=\"p_title\">A Library for Formal Verification of Low-level Programs</p>"
echo "<dl class=\"dl_main\">"
for dir in $*; do
    currentdir=`pwd`
    cd $dir
    echo "<dt class=\"dt_main\"><span class=\"bfont\">"$dir/"</span>: "
    cat README.doc
    echo "</dt>"
    echo "<dd class=\"dd_main\">"
    if [ $dir == 'lib' ]; then
	for i in *.v; do
	    if [[ "$i" != *goto* ]] && [[ "$i" != *while* ]] && [[ "$i" != *compile* ]]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Hoare logic modules:</p>"
	for i in *.v; do
	    if [[ "$i" == *goto* ]] || [[ "$i" == *while* ]] || [[ "$i" == *compile* ]] ; then
		print_filename $dir $i
	    fi
	done
    fi
    if [ $dir == 'seplog' ]; then
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
    fi
    if [ $dir == 'cryptoasm' ]; then
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
    fi
    if [ $dir == 'begcd' ]; then
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
# 	echo "<div id=\"kamoku\">Multi-precision unsigned arithmetic</div>"

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

#	print_function_begcd_special $dir 'In progress &rarr;' 'library_interfaces.v'

	echo "</ul>"
	echo "</div>"
	echo "<p class=\"sublib\">Application to the binary extended gcd algorithm algorithm:</p>"
	for i in *.v; do
	    if [[ "$i" == begcd*.v ]]; then
		print_filename $dir $i
	    fi
	done
    fi
#    if [ $dir == 'bbs_unpredictable' ]; then
#	echo "<p class=\"sublib\">Certifying Assembly with Formal Cryptographic Proofs: the Case of BBS:</p>"
#	for i in *.v; do
#	    print_filename $dir $i
#	done
#    fi
    if [ $dir == 'seplogC' ]; then
	echo "<p class=\"sublib\">Formalization of a subset of the C programming language and its Separation logic:</p>"
	for i in *.v; do
	    C_cond $i
	    if [ $? -eq 1 ]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Formal specification of TLS network packets (see <a href=\"http://tools.ietf.org/html/rfc5246\">RFC 5246</a>):</p>"
	print_filename $dir "rfc5246.v"
	echo "<p class=\"sublib\">Application to the formal verification of network packet decoder functions taken from <a href=\"http://polarssl.org\">PolarSSL</a>:</p>"
	for i in *.v; do
	    POLAR_cond $i
	    if [ $? -eq 1 ]; then
		print_filename $dir $i
	    fi
	done
    fi
    echo "</dd>"
    cd $currentdir
done
echo "</dl>"
echo ""
