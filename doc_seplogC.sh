source ./doc_functions.sh

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

echo "<title>TITLE</title>"
echo "</head>"
echo "<body>"
dir="seplogC"
cd $dir
    echo "<dt class=\"dt_main\"><span class=\"bfont\">"$dir/"</span>: "
cat README.doc
    echo "</dt>"
	echo "<p class=\"sublib\">Formalization of a subset of the C programming language and its Separation logic:</p>"
	for i in *.v; do
	    C_cond $i
	    if [ $? -eq 1 ]; then
		print_filename $dir $i
	    fi
	done
	echo "<p class=\"sublib\">Formal specification of TLS network packets (see <a href=\"http://tools.ietf.org/html/rfc5246\" target=\"_top\" >RFC 5246</a>):</p>"
	print_filename $dir "rfc5246.v"
	echo "<p class=\"sublib\">Application to the formal verification of network packet decoder functions taken from PolarSSL (now <a href=\"https://tls.mbed.org/\" target=\"_top\" >mbed TLS</a>):</p>"
	for i in *.v; do
	    POLAR_cond $i
	    if [ $? -eq 1 ]; then
		print_filename $dir $i
	    fi
	done
