import setuptools

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setuptools.setup(
    name="rfm_mc-jondow8", # Replace with your own username
    version="0.0.1",
    author="Jonah Leander Hoff",
    author_email="jonah.hoff@outlook.com",
    description="A framework for restrictive formula based model counting",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="",
    packages=setuptools.find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)