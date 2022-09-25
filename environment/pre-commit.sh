echo "Running pre-commit hook..."

check_license_notes() {
    for filename in `find lib -regextype posix-extended -regex ".*\.[hc]pp"`; do
        case `cat $filename` in
            "/*"*) true;;
                *) echo "Expected license comment in $filename" && exit 1;;
        esac
    done
}

format() {
    doxygen
    find lib -regextype posix-extended -regex ".*\.[hc]pp" | xargs clang-format -i
    git add --update
}

check_license_notes
format
