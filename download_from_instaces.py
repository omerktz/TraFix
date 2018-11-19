import boto3
import paramiko
import os
import parmap

ec2 = boto3.client('ec2')

def handle_instance((dir, dns, i)):
	client = paramiko.SSHClient()
	client.set_missing_host_key_policy(paramiko.AutoAddPolicy)
	client.connect(dns, username='ubuntu', key_filename='omer1.pem')
	sin, sout, serr = client.exec_command('cd Codenator; tar -czf tmp.tar.gz output* log*')
	sout.channel.recv_exit_status()
	sftp = client.open_sftp()
	sftp.chdir('Codenator')
	sftp.get('tmp.tar.gz', os.path.join(dir, 'tmp{0}.tar.gz'.format(i)))
	sin, sout, serr = client.exec_command('cd Codenator; rm tmp.tar.gz')
	sout.channel.recv_exit_status()
	client.close()

def extract_instance((dir, dns, i)):
	os.system('cd {0}; tar -xzf tmp{1}.tar.gz; rm tmp{1}.tar.gz; cd - > /dev/null'.format(dir, i))

def handle_batch(batch, instances):
	print 'Downloading batch '+batch+'... ',
	dir = 'downloaded_'+batch
	dnss = map(lambda (x,y): (dir, x, y), instances)
	os.makedirs(dir)
	parmap.map(handle_instance, dnss)
	parmap.map(extract_instance, dnss)
	print 'Done'

batch = 'nested_unoptimized_x86'
instances = [('ec2-18-206-172-203.compute-1.amazonaws.com', 0), ('ec2-54-86-115-196.compute-1.amazonaws.com', 1), ('ec2-54-82-232-14.compute-1.amazonaws.com', 3), ('ec2-34-229-6-40.compute-1.amazonaws.com', 4), ('ec2-34-230-77-152.compute-1.amazonaws.com', 5)]
handle_batch(batch, instances)

batch = 'nested_x86'
instances = [('ec2-34-229-18-242.compute-1.amazonaws.com', 0), ('ec2-54-237-233-121.compute-1.amazonaws.com', 1), ('ec2-34-228-140-83.compute-1.amazonaws.com', 2), ('ec2-54-226-113-211.compute-1.amazonaws.com', 3), ('ec2-18-208-182-221.compute-1.amazonaws.com', 4)]
handle_batch(batch, instances)

batch = 'small_x86'
instances = [('ec2-54-165-255-117.compute-1.amazonaws.com', 0), ('ec2-52-205-253-177.compute-1.amazonaws.com', 1), ('ec2-52-23-229-16.compute-1.amazonaws.com', 2), ('ec2-54-205-9-160.compute-1.amazonaws.com', 3), ('ec2-18-234-164-213.compute-1.amazonaws.com', 4)]
handle_batch(batch, instances)

batch = 'x86'
instances = [('ec2-52-90-155-38.compute-1.amazonaws.com', 0), ('ec2-100-26-47-222.compute-1.amazonaws.com', 1), ('ec2-54-208-173-172.compute-1.amazonaws.com', 2), ('ec2-100-26-145-48.compute-1.amazonaws.com', 3), ('ec2-54-84-208-244.compute-1.amazonaws.com', 4)]
handle_batch(batch, instances)
