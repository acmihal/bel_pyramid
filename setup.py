from setuptools import setup, find_packages

setup(
    name='bel_pyramid',
    version='0.1.0',
    packages=find_packages(where='src'),
    package_dir={'': 'src'},
    install_requires=['z3'],
    entry_points={
        'console_scripts': [
            'bel_pyramid=bel_pyramid:main',
        ],
    },
)
