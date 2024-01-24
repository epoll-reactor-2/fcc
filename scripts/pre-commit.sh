echo "Running pre-commit hook..."

check_license_notes() {
    for filename in `find lib -name '*.c' -o -name '*.h'`; do
        case `head -c 2 $filename` in
            "/*"*) true;;
                *) echo "Expected license comment in $filename" && exit 1;;
        esac
    done
}

static_analysis() {
    make static_analysis
}

check_license_notes
static_analysis