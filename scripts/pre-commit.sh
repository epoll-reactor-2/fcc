echo "Running pre-commit hook..."

check_license_notes() {
    for filename in `find lib -regextype posix-extended -regex ".*\.(h|cpp)"`; do
        case `cat $filename` in
            "/*"*) true;;
                *) echo "Expected license comment in $filename" && exit 1;;
        esac
    done
}

check_license_notes
