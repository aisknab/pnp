FROM node:20-bookworm-slim
WORKDIR /workspace/pnp
COPY package.json package-lock.json ./
RUN npm ci
COPY . .
CMD ["npm", "run", "pnp:verify"]
