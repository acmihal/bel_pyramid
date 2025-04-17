from bel_pyramid.bel_pyramid import main
from io import StringIO
from unittest.mock import patch
import pytest
import sys

def test_missing_args(capsys):
    with pytest.raises(SystemExit) as excinfo:
        main()
    captured = capsys.readouterr()
    assert excinfo.type == SystemExit
    assert captured.err.startswith("usage")

def test_provided_args(capsys):
    testargs = ["bel_pyramid", "1"]
    with patch.object(sys, 'argv', testargs):
        main()
    captured = capsys.readouterr()
    assert captured.out.startswith("Solving Bel's Pyramid for 1 levels.")

def test_help(capsys):
    testargs = ["bel_pyramid", "-h"]
    with patch.object(sys, 'argv', testargs):
        with pytest.raises(SystemExit) as excinfo:
            main()
    captured = capsys.readouterr()
    assert excinfo.type == SystemExit
    assert captured.out.startswith("usage")
