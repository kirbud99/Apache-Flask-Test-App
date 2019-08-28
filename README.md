Build the image once you are in the folder.

`docker build -t apache-flask .`

Run the image once you are in the folder.
`docker run -d -p 80:80 --name=apache-flask apache-flask`

Access at localhost:80
